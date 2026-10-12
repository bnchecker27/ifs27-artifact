-- service.lua — the RPM service core: protocol dispatch + model store.
--
-- Written in plain Lua so the SAME code runs in the native LuaJIT
-- server (server.lua, ffi sockets) and inside the browser web worker
-- (the WASM Lua runtime hosted by server/src/service.mjs).  Both hosts
-- inject the dependencies as source strings:
--
--   local dispatch = assert(load(service_src))(json_src, validate_src, sources)
--   response_json = dispatch(request_json, hooks)
--
-- `sources` is an optional table {["module.name"] = source, ...} used by
-- the web worker (no filesystem) to populate package.preload for the
-- formula parser modules.  The native server sets package.path/cpath and
-- leaves this nil.
--
-- `hooks` is an optional table the host may supply:
--   save(text)   — persist the model JSON (the native server writes the
--                  model file; the worker leaves it to the JS layer)
--
-- Protocol (one JSON object per frame):
--   {method="ping", payload}        -> {method="pong", payload}
--   {method="eval", code}           -> {method="eval_result", result=[...]}
--   {method="get_model"}            -> {method="model", model={...}|null}
--   {method="set_model", model}     -> stores + validates ->
--                                      {method="report", problems=[...]}
--   {method="restore_model", model} -> startup restore; no save, but a
--                                      report is still produced
--   {method="check_formula", formula}-> {method="formula_report",
--                                         ok=true} or
--                                      {method="formula_report",
--                                         ok=false, error="...", from=?, to=?}

local json_src, validate_src, sources = ...

local unpack = table.unpack or unpack

local json = assert(load(json_src, "json.lua"))()
local validate_model = assert(load(validate_src, "validate.lua"))()

-- The web worker has no filesystem; the host passes the parser sources.
if type(sources) == "table" then
    for name, src in pairs(sources) do
        package.preload[name] = function()
            local chunk, err = load(src, name)
            if not chunk then error(err) end
            return chunk()
        end
    end
end

local EXAMPLES
local ok, examples_mod = pcall(require, "server.lua.examples")
if ok and type(examples_mod) == "table" then
    EXAMPLES = examples_mod
end

local function get_parser()
    local ok, parse = pcall(require, "logic.parser_bn_logic")
    if not ok then
        error("formula parser not available: " .. tostring(parse))
    end
    return parse
end

local function get_features()
    local ok, mod = pcall(require, "lib.features")
    if not ok then
        error("feature table not available: " .. tostring(mod))
    end
    return mod
end

-- Optional features ("cond", "marginal", "chart", "all") are off by
-- default; a request opts in via its `features` field.
local function msg_features(msg)
    return get_features().parse(msg.features)
end

local explainer = nil
local function get_explainer()
    if explainer == nil then
        local ok, mod = pcall(require, "logic.explainer")
        if ok then
            explainer = mod
        else
            explainer = false
        end
    end
    return explainer
end

local stored_model = nil
local stored_model_key = nil

-- Return a structural fingerprint of a model that ignores presentation
-- fields (id, x, y, desc) so we can tell whether a stored/normalised
-- model still matches one of the built-in examples.
local function model_fingerprint(model)
    if type(model) ~= "table" or type(model.nodes) ~= "table" then
        return nil
    end
    local node_map = {}
    local id_to_name = {}
    for i, n in ipairs(model.nodes) do
        if type(n) == "table" then
            local name = tostring(n.name or "")
            local outs = {}
            if type(n.outcomes) == "table" then
                for _, v in ipairs(n.outcomes) do
                    table.insert(outs, tostring(v))
                end
            end
            local cpt_rows = {}
            if type(n.cpt) == "table" then
                for _, row in ipairs(n.cpt) do
                    if type(row) == "table" then
                        local cells = {}
                        for _, v in ipairs(row) do
                            table.insert(cells, tostring(tonumber(v) or v))
                        end
                        table.insert(cpt_rows, table.concat(cells, ","))
                    end
                end
            end
            local rec = {
                name = name,
                outs = table.concat(outs, ","),
                cpt = table.concat(cpt_rows, ";"),
            }
            table.insert(node_map, rec)
            id_to_name[tonumber(n.id) or i] = name
        end
    end
    table.sort(node_map, function(a, b)
        if a.name ~= b.name then return a.name < b.name end
        return a.outs < b.outs
    end)
    local edges = {}
    for _, e in ipairs(model.edges or {}) do
        local from = id_to_name[tonumber(e.from)] or tostring(e.from)
        local to = id_to_name[tonumber(e.to)] or tostring(e.to)
        table.insert(edges, from .. "->" .. to)
    end
    table.sort(edges)
    local parts = {}
    for _, n in ipairs(node_map) do
        table.insert(parts, n.name .. "[" .. n.outs .. "]:" .. n.cpt)
    end
    return table.concat(parts, "|") .. "#" .. table.concat(edges, "|")
end

local function find_example_key(model)
    if not EXAMPLES then return nil end
    local fp = model_fingerprint(model)
    if not fp then return nil end
    for _, m in pairs(EXAMPLES.models) do
        if type(m) == "table" and m.model then
            if model_fingerprint(m.model) == fp then
                return m.key
            end
        end
    end
    return nil
end

local function get_model_names(model)
    local names = {}
    if type(model) == "table" and type(model.nodes) == "table" then
        for _, n in ipairs(model.nodes) do
            if type(n) == "table" and type(n.name) == "string" and n.name ~= "" then
                table.insert(names, n.name)
            end
        end
    end
    return names
end

local function get_model_outcomes(model)
    local seen = {}
    local out = {}
    if type(model) == "table" and type(model.nodes) == "table" then
        for _, n in ipairs(model.nodes) do
            if type(n) == "table" and type(n.outcomes) == "table" then
                for _, v in ipairs(n.outcomes) do
                    local sv = tostring(v)
                    if not seen[sv] then
                        seen[sv] = true
                        table.insert(out, sv)
                    end
                end
            end
        end
    end
    return out
end

-- assigned a lazy_module proxy further down (with varterm); the
-- functions below use it at call time only, but the local must be
-- DECLARED before them or they would read the global instead
local dist_family

local function get_model_node_info(model, name)
    if type(model) ~= "table" or type(model.nodes) ~= "table" then return nil end
    for _, n in ipairs(model.nodes) do
        if type(n) == "table" and n.name == name and type(n.outcomes) == "table" then
            local set = {}
            for _, v in ipairs(n.outcomes) do
                set[tostring(v)] = true
            end
            return {name = n.name, outcomes = n.outcomes, set = set}
        end
    end
    return nil
end

-- A model node is real-valued when every declared outcome is an actual
-- number (feature "numval"); a numeric string ("0.5") stays a string
-- outcome.  Mixed domains are rejected by validate_model.
local function node_is_numeric(node)
    if type(node) ~= "table" or type(node.outcomes) ~= "table"
       or #node.outcomes == 0 then
        return false
    end
    for _, v in ipairs(node.outcomes) do
        if type(v) ~= "number" then
            return false
        end
    end
    return true
end

-- true when `name` is a real-valued model variable
local function numeric_name(model, name)
    local info = name and get_model_node_info(model, name) or nil
    return info ~= nil and node_is_numeric(info)
end

-- "numval": the JSON model format cannot distinguish a numeric intent
-- from a numeric-looking outcome name — the UI's outcome fields are
-- plain text, so "0.0"/"1.0" arrive as strings.  A node whose outcome
-- tokens ALL convert to finite numbers is coerced to a real-valued
-- domain — all-or-nothing, matching the no-mixing rule (the same
-- treatment BIF domains get in parser_bif).  Runs before
-- validate_model so numeric collisions ("0" vs "00") surface as
-- duplicate_value; a node that cannot fully convert stays strings.
local function coerce_numeric_outcomes(model, fset)
    if not (fset and fset.numval and type(model) == "table") then
        return
    end
    for _, n in ipairs(model.nodes or {}) do
        local outc = type(n) == "table" and n.outcomes or nil
        if type(outc) == "table" and #outc > 0 then
            local converted, numeric, allnum = {}, true, true
            for i, v in ipairs(outc) do
                if type(v) ~= "number" then allnum = false end
                local num = type(v) == "number" and v
                    or type(v) == "string" and tonumber(v) or nil
                if not num or num ~= num
                   or num == math.huge or num == -math.huge then
                    numeric = false
                    break
                end
                converted[i] = num
            end
            if numeric and not allnum then n.outcomes = converted end
        end
    end
end

-- the arithmetic-infix tokens: all four are builtin (the former
-- "arith" feature gate only ever held + and ÷)
local function arith_tokens(feature_set)
    return {"+", "−", "×", "÷"}
end

-- the declared domain of a MUX selector / RENAME source term —
-- forward-declared: it parses the term and consults varterm.domain,
-- both only available further down
local varterm_source_domain
-- The LET-bindings scope at a position (feature "let"): walk the
-- formula up to pos, tracking parenthesis depth and a stack of open
-- "let" frames.  A frame opens on a LET keyword; a binding name
-- becomes visible when its binding closes (at the ';' that starts the
-- next binding or at the let's 'IN'); a frame closes when the depth
-- drops below the let's own depth — its body lives at that depth — so
-- "P(LET X = e IN X = 1) ∧ X" only offers X inside the parens.
--
-- Returns {names = {...}, expect = …}: the bound names visible at pos
-- (outer lets first) and the innermost frame's phase — "name" (a
-- binding name goes here), "assign" (name read, '=' expected), "rhs"
-- (inside a right side) or "body" — so the suggestion code can offer
-- bound names as variable candidates and tell a name slot from a
-- right-side or body slot.
local function let_scope_at(formula, pos)
    local depth = 0
    local stack = {}
    local i = 1
    local n = math.min(#formula, pos - 1)
    while i <= n do
        local ch = formula:sub(i, i)
        if ch == "(" or ch == "[" then
            depth = depth + 1
            i = i + 1
        elseif ch == ")" or ch == "]" then
            depth = depth - 1
            while #stack > 0 and stack[#stack].depth > depth do
                stack[#stack] = nil
            end
            i = i + 1
        elseif ch:match("[%a_]") then
            local j = i
            while j <= #formula
                  and formula:sub(j, j):match("[%a%d_]") do
                j = j + 1
            end
            local word = formula:sub(i, j - 1)
            if word == "LET" then
                stack[#stack + 1] =
                    {depth = depth, expect = "name",
                     pending = nil, order = {}, bound = {}, rhs = {}}
            elseif word == "IN"
                   and (i == 1
                        or not formula:sub(i - 1, i - 1)
                               :match("[%a%d_]")) then
                -- the keyword needs a leading boundary too — the IN
                -- of "5IN" continues the number's token run and is
                -- neither the tail keyword nor a legal binding name
                -- an IN belongs to the innermost frame still in its
                -- bindings; frames already in their body close first
                while #stack > 0
                      and stack[#stack].depth == depth
                      and stack[#stack].expect == "body" do
                    stack[#stack] = nil
                end
                local f = stack[#stack]
                if f and f.depth == depth
                   and (f.expect == "rhs" or f.expect == "assign"
                        or f.expect == "name") then
                    if f.pending then
                        if not f.bound[f.pending] then
                            f.bound[f.pending] = true
                            f.order[#f.order + 1] = f.pending
                            if f.assign_at then
                                f.rhs[f.pending] =
                                    formula:sub(f.assign_at + 1, i - 1)
                            end
                        end
                        f.pending = nil
                    end
                    f.expect = "body"
                    f.body_at = j
                end
            else
                local f = stack[#stack]
                -- an "IN" rejected above is not a name either — the
                -- parser's -KwName reserves it like LET
                if f and f.depth == depth and f.expect == "name"
                   and word ~= "IN" then
                    f.pending = word
                    f.expect = "assign"
                end
            end
            i = j
        elseif ch == "=" then
            local f = stack[#stack]
            if f and f.depth == depth and f.expect == "assign" then
                f.expect = "rhs"
                f.assign_at = i
            end
            i = i + 1
        elseif ch == ";" then
            while #stack > 0
                  and stack[#stack].depth == depth
                  and stack[#stack].expect == "body" do
                stack[#stack] = nil
            end
            local f = stack[#stack]
            if f and f.depth == depth and f.expect == "rhs" then
                if f.pending then
                    if not f.bound[f.pending] then
                        f.bound[f.pending] = true
                        f.order[#f.order + 1] = f.pending
                        if f.assign_at then
                            f.rhs[f.pending] =
                                formula:sub(f.assign_at + 1, i - 1)
                        end
                    end
                    f.pending = nil
                end
                f.expect = "name"
            end
            i = i + 1
        else
            i = i + 1
        end
    end
    local names, seen, rhs = {}, {}, {}
    for _, f in ipairs(stack) do
        for _, nm in ipairs(f.order) do
            if not seen[nm] then
                seen[nm] = true
                names[#names + 1] = nm
                rhs[nm] = f.rhs[nm]
            end
        end
    end
    local top = stack[#stack]
    return {names = names, expect = top and top.expect or nil,
            body_at = top and top.body_at or nil,
            assign_at = top and top.assign_at or nil,
            rhs = rhs}
end

-- scalar moment queries over a random variable — each carries its own
-- feature flag ("expect"/"variance"/"sd"); the operand is a
-- variable-valued term like a P marginal query
local MOMENT_OPS = {expect = true, variance = true, sd = true}

local logical_operators = {["not"] = true, ["and"] = true, ["nand"] = true,
                           ["or"] = true, ["nor"] = true, ["implication"] = true,
                           ["biimplication"] = true, ["xor"] = true}
local compare_operators = {["less"] = true, ["less_or_equal"] = true, ["equal"] = true,
                           ["greater_or_equal"] = true, ["greater"] = true}
local arithmetic_operators = {["plus"] = true, ["minus"] = true,
                              ["times"] = true, ["divide"] = true}

-- classify a LET-bound name by its bound right side: "boolq" when the
-- right side is a claim (the name is already a complete boolean
-- operand — comparisons/interventions on it never rescue), "number"
-- when it evaluates to a number (a scalar like P(..)/E(..)/a numexpr,
-- or a varterm whose static domain is all-numeric), nil for anything
-- else (a variable-valued term over a non-numeric domain — behaves
-- like a plain variable name).  The right side text is the slice of
-- the formula between the binding's '=' and its ';'/'IN'.
local function bound_rhs_kind(rhs, model, feature_set)
    if not (rhs and feature_set) then return nil end
    rhs = rhs:match("^%s*(.-)%s*$")
    local parse = get_parser()
    local ok, ast = pcall(parse, rhs, feature_set)
    if not ok or type(ast) ~= "table" then return nil end
    local op = ast:get_type() == "operator"
        and ast:get_operator_name() or nil
    if op and (compare_operators[op] or logical_operators[op]
               or op == "modify_probability" or op == "let") then
        return "boolq"
    end
    if ast:get_type() == "value" or op == "prob"
       or (op and MOMENT_OPS[op])
       or (op and arithmetic_operators[op]) then
        return "number"
    end
    -- a variable-valued term (name, literal, conditional): numeric
    -- when its static domain is all numbers
    local dom = varterm_source_domain
        and varterm_source_domain(model, rhs, feature_set)
    if type(dom) == "table" and #dom > 0 then
        for _, v in ipairs(dom) do
            if type(v) ~= "number" then return nil end
        end
        return "number"
    end
    return nil
end

local function model_to_bn(model, make_bn)
    local bn = make_bn()
    local byId = {}
    for _, n in ipairs(model.nodes or {}) do
        byId[n.id] = n
    end
    -- variables and their values
    for _, n in ipairs(model.nodes or {}) do
        bn:set_values(n.name, n.outcomes)
    end
    -- parents in edge order
    local parents_of = {}
    for _, e in ipairs(model.edges or {}) do
        parents_of[e.to] = parents_of[e.to] or {}
        table.insert(parents_of[e.to], e.from)
    end
    -- conditional probabilities
    for _, n in ipairs(model.nodes or {}) do
        local parents = parents_of[n.id] or {}
        local np = #parents
        local nv = #n.outcomes
        local strides = {}
        local stride = 1
        for p = np, 1, -1 do
            local pn = byId[parents[p]]
            strides[p] = stride
            stride = stride * math.max(1, pn and #pn.outcomes or 1)
        end
        for r = 0, #n.cpt - 1 do
            local cond = {}
            for p = 1, np do
                local pid = parents[p]
                local pn = byId[pid]
                if pn then
                    local cnt = #pn.outcomes
                    local idx = math.floor(r / strides[p]) % cnt
                    cond[pn.name] = pn.outcomes[idx + 1]
                end
            end
            local probs = {}
            for c = 1, nv do
                local v = n.cpt[r + 1][c]
                local num = tonumber(v)
                if num == nil then
                    error({key = "non_numeric_cpt",
                           parameters = {node = n.name, row = r + 1, col = c, value = tostring(v)}})
                end
                probs[n.outcomes[c]] = num
            end
            bn:set_probabilies(n.name, cond, probs)
        end
    end
    return bn
end

local cached_modules = {}
local function require_module(name)
    local c = cached_modules[name]
    if c ~= nil then
        -- entries are always pairs {result, err} so a cached failure
        -- keeps its original error message instead of reporting nil
        return c[1], c[2]
    end
    local ok, m = pcall(require, name)
    if not ok then
        cached_modules[name] = {false, m}
        return false, m
    end
    cached_modules[name] = {m}
    return m
end

-- A probability-distribution result is a table of name -> probability;
-- a MAP/MPE assignment is the same shape but with outcome-name string
-- values, which is what tells the two apart.  The client charts the
-- result when this payload is present, so the order mirrors the
-- displayed string: __order first, alphabetical otherwise.
local function dist_payload(res)
    if type(res) ~= "table" then return nil end
    local items = {}
    local mt = getmetatable(res)
    local order = mt and mt.__order
    if order then
        for _, k in ipairs(order) do
            local v = res[k]
            if type(v) ~= "number" then return nil end
            items[#items + 1] = {name = tostring(k), p = v}
        end
    else
        for k, v in pairs(res) do
            if type(v) ~= "number" then return nil end
            items[#items + 1] = {name = tostring(k), p = v}
        end
        table.sort(items, function(a, b) return a.name < b.name end)
    end
    if #items == 0 then return nil end
    return items
end

local function format_result(res)
    if type(res) == "boolean" then
        return res and "true" or "false"
    elseif type(res) == "number" then
        return tostring(res)
    elseif type(res) == "table" then
        -- MAP/MPE assignment tables share their rendering with the
        -- displays the model checker composes for compound formulas.
        local rd = require_module("model_checker.result_display")
        if rd then
            return rd.assignment(res)
        end
        local parts = {}
        for k, v in pairs(res) do
            table.insert(parts, tostring(k) .. " = " .. tostring(v))
        end
        table.sort(parts)
        return table.concat(parts, ", ")
    else
        return tostring(res)
    end
end

-- Cached BN and semantic validation state
local cached_bn = nil
local cached_for_model = nil

local function get_cached_bn()
    if not stored_model then
        return nil
    end
    if cached_for_model ~= stored_model then
        cached_bn = nil
    end
    if not cached_bn then
        local make_bn, _ = require_module("bayesian_network.bayesian_network")
        if not make_bn then
            return nil
        end
        local ok, bn = pcall(model_to_bn, stored_model, make_bn)
        if not ok then
            return nil
        end
        cached_bn = bn
        cached_for_model = stored_model
    end
    return cached_bn
end

local function collect_bn_info(bn, feature_set)
    local variables = {}
    local var_values = {}
    local var_outcomes = {}
    local all_values = {}
    local numeric_vars = {}
    local var_num_values = {}
    for _, name in ipairs(bn:get_variables()) do
        variables[name] = true
        local values = bn:get_values_or_nil(name) or {}
        local vs = {}
        local nvs = {}
        local numeric = #values > 0
        for _, v in ipairs(values) do
            local sv = tostring(v)
            vs[sv] = true
            all_values[sv] = true
            -- a real-valued outcome is an actual number: a numeric
            -- string ("0.5") stays a string value
            if type(v) == "number" then
                nvs[v] = true
            else
                numeric = false
            end
        end
        var_values[name] = vs
        var_outcomes[name] = values
        if numeric then
            numeric_vars[name] = true
            var_num_values[name] = nvs
        end
    end
    return {variables = variables, var_values = var_values,
            var_outcomes = var_outcomes,
            all_values = all_values, features = feature_set,
            numeric_vars = numeric_vars, var_num_values = var_num_values}
end

local SEMANTIC_ERRORS = {
    unknown_identifier = function(p)
        return "unknown identifier '" .. tostring(p.name) .. "'"
    end,
    not_a_variable = function(p)
        return "'" .. tostring(p.name) .. "' is not a variable"
    end,
    not_a_value = function(p)
        return "'" .. tostring(p.value) .. "' is not a value"
    end,
    not_boolean = function(p)
        return "this expression is not boolean"
    end,
    not_numeric = function(p)
        return "this expression is not numeric"
    end,
    not_numeric_variable = function(p)
        return "variable '" .. tostring(p.name) .. "' is not real-valued"
    end,
    quantifier_not_allowed = function(p)
        return p.quantifier:upper() .. "(...) cannot be used here"
    end,
    prob_nested = function(p)
        return "P(...) cannot contain " .. p.quantifier .. "(...)"
    end,
    comparison_no_variable = function(p)
        return "a comparison needs at least one variable"
    end,
    comparison_incomparable = function(p)
        return "variables '" .. tostring(p.left) .. "' and '" .. tostring(p.right) .. "' are not comparable"
    end,
    invalid_value_for = function(p)
        return "'" .. tostring(p.value) .. "' is not a value of variable '" .. tostring(p.variable) .. "'"
    end,
    map_query_not_variable = function(p)
        return "MAP query '" .. tostring(p.name) .. "' is not a variable"
    end,
    idp_var_not_variable = function(p)
        return "IDP argument '" .. tostring(p.name) .. "' is not a variable"
    end,
    infl_var_not_variable = function(p)
        return "INFL argument '" .. tostring(p.name) .. "' is not a variable"
    end,
    modify_target_not_variable = function(p)
        return "intervention target '" .. tostring(p.name) .. "' is not a variable"
    end,
    dist_bad_probability = function(p)
        return "probability '" .. tostring(p.value) .. "' in DIST is not in [0,1]"
    end,
    dist_mixed_domain = function(p)
        return "DIST outcomes must be all names or all numbers"
    end,
    dist_not_normalized = function(p)
        return "probabilities in DIST do not sum to 1 (sum: " .. tostring(p.sum) .. ")"
    end,
    pdist_args = function(p)
        return p.family .. "(...) takes " .. tostring(p.expected)
               .. " argument(s), got " .. tostring(p.got)
    end,
    pdist_param = function(p)
        return p.family .. " parameter '" .. tostring(p.param)
               .. "' must be " .. tostring(p.want)
               .. " (got '" .. tostring(p.value) .. "')"
    end,
    rename_source_not_variable = function(p)
        return "RENAME's first argument is not a variable term"
    end,
    rename_missing_outcome = function(p)
        return "outcome '" .. tostring(p.value) .. "' of '" .. tostring(p.variable) .. "' is not renamed"
    end,
    rename_mixed_domain = function(p)
        return "renamed outcomes must be all names or all numbers"
    end,
    rename_nonadjacent = function(p)
        return "renamed outcome '" .. tostring(p.value) .. "' appears in non-adjacent entries"
    end,
    mux_source_not_variable = function(p)
        return "MUX's first argument is not a variable term"
    end,
    mux_branch_not_variable = function(p)
        return "MUX branches must be variable terms"
    end,
    mux_bad_entry = function(p)
        return "invalid MUX entry (expected outcome ↦ variable or variable ↦ probability)"
    end,
    mux_missing_outcome = function(p)
        return "outcome '" .. tostring(p.value) .. "' of '" .. tostring(p.variable) .. "' has no MUX branch"
    end,
    mux_mixed_domain = function(p)
        return "MUX branches must have all-numeric or all-name domains"
    end,
    mux_ambiguous_domain = function(p)
        return "MUX branch domains have no unique common order"
    end,
    mux_conflicting_domain = function(p)
        return "MUX branch domains disagree on outcome order"
    end,
    numval_required = function(p)
        return "numeric outcomes need the numval feature"
    end,
    duplicate_value = function(p)
        return "duplicate outcome '" .. tostring(p.value) .. "' in '" .. tostring(p.variable) .. "'"
    end,
    incomplete_formula = function(p)
        return "the formula is incomplete: fill in the □ placeholders"
    end,
    let_redefines = function(p)
        return "'" .. tostring(p.name) .. "' already names a variable or an earlier binding"
    end,
    let_rhs = function(p)
        return "the right side of '" .. tostring(p.name) .. "' cannot be bound to a variable"
    end,
    node_formula_kind = function(p)
        return "a node formula must be a variable term or a Boolean claim"
    end,
    node_formula_construct = function(p)
        return "'" .. tostring(p.construct) .. "' cannot be used in a node formula"
    end,
    node_formula_nonparent = function(p)
        return "'" .. tostring(p.name) .. "' is not a parent of '" .. tostring(p.node) .. "'"
    end,
}

local function make_semantic_error(key, positional, params)
    params = params or {}
    return {key = key, msg = SEMANTIC_ERRORS[key](params), positional = positional, parameters = params}
end

local function pos_to_table(pos)
    if not pos then
        return nil, nil
    end
    return pos.from, pos.to
end

-- forward declarations: the annotation-suggestion helpers are defined
-- after the lazy_module proxies they defer through (suggestions is the
-- logic.suggestions proxy assigned below)
local suggestions
local suggest_env, resolve_suggests, probe_suggests

-- the continuation payloads anchored on the flagged span itself:
-- probe at to_pos+1 and keep the ops payload whose `after` node spans
-- exactly [from,to_pos] — that node is the real operand AST, so the
-- completability gates run on it instead of on the token's text
local function span_ops(parse, formula, feature_set, from, to_pos, needs)
    local pl = probe_suggests(parse, formula, to_pos + 1, feature_set)
    for _, p in ipairs((pl and pl.suggest) or {}) do
        local a = p.after
        if p.kind == "ops" and type(a) == "table" and a.positional
           and a.positional.from == from
           and a.positional.to == to_pos
           and (needs == nil or p.needs == needs) then
            return p
        end
    end
    return nil
end

local function semantic_error_to_report(err, seq, formula, feature_set)
    local from, to_pos = pos_to_table(err.positional)
    local expected = nil
    -- A semantic error that flags the trailing token can still be fixed by
    -- appending; mid-formula errors cannot, so nothing is suggested there.
    if formula and from and to_pos
       and formula:sub(to_pos + 1):match("^%s*$") then
        local token = formula:sub(from, to_pos)
        local parse = get_parser()
        local function completions()
            -- the candidates valid for the token's own slot: probe the
            -- grammar at the flagged token's start and take the suffix
            -- completions of whatever that slot offers — keywords,
            -- model names, outcomes — all gated by the payloads there
            local pl = probe_suggests(parse, formula, from, feature_set)
            local toks = resolve_suggests(stored_model, formula, from,
                                          pl, feature_set)
            if not toks then return {} end
            local sufs, seen = {}, {}
            for _, s in ipairs(suggestions.partial_suffixes(toks, token)) do
                if not seen[s] then
                    seen[s] = true
                    sufs[#sufs + 1] = s
                end
            end
            return sufs
        end
        if err.key == "not_boolean" then
            -- a trailing identifier/number leaf still becomes boolean via
            -- a comparison — "¬Grade" -> "¬(Grade = High)" — since the
            -- compare operators bind tighter than the logical ones.  The
            -- token itself must be able to head a comparison (a variable,
            -- an outcome or a number); otherwise only completing the name
            -- keeps a rescue possible ("¬Gr" -> "ade").
            local is_operand = token:match("^%d") ~= nil
            if not is_operand then
                is_operand = get_model_node_info(stored_model, token) ~= nil
            end
            if not is_operand then
                for _, v in ipairs(get_model_outcomes(stored_model)) do
                    if v == token then
                        is_operand = true
                        break
                    end
                end
            end
            if not is_operand then
                -- the flagged span may be a whole conditioned term —
                -- "x ∧ B | C" flags "B | C" — whose LAST leaf is the
                -- rescuable operand: "B | C" -> "B | C = c"
                local tail = token:match("([%a_][%w_]*)%s*$")
                    or token:match("(%d[%d%.]*)%s*$")
                if tail then
                    is_operand = tail:match("^%d") ~= nil
                        or get_model_node_info(stored_model, tail) ~= nil
                    if not is_operand and feature_set
                       and feature_set.let then
                        local ls = let_scope_at(formula, to_pos + 1)
                        for _, nm in ipairs(ls and ls.names or {}) do
                            if nm == tail then
                                is_operand = true
                                break
                            end
                        end
                    end
                elseif token:match("%)%s*$") then
                    -- "… | DIST(..)" ends in a varterm literal
                    is_operand = true
                end
            end
            if is_operand then
                expected = {"=", "≤", "≥", "<", ">"}
                -- a numeric operand (number, real-valued variable,
                -- numeric-domain literal or LET-bound scalar) also
                -- continues into arithmetic — "Die1" -> "Die1 + Die2",
                -- "MUX(S, a ↦ 0, b ↦ 1)" -> "… + 1"
                if feature_set and feature_set.numvar then
                    local numeric = token:match("^%d") ~= nil
                        or numeric_name(stored_model, token)
                    if not numeric and token:match("%)%s*$") then
                        local dom = varterm_source_domain
                            and varterm_source_domain(stored_model, token,
                                                      feature_set)
                        if type(dom) == "table" and #dom > 0 then
                            numeric = true
                            for _, v in ipairs(dom) do
                                if type(v) ~= "number" then
                                    numeric = false
                                    break
                                end
                            end
                        end
                    end
                    if not numeric and feature_set.let then
                        local ls = let_scope_at(formula, to_pos + 1)
                        local tail = token:match("([%a_][%w_]*)%s*$")
                        if ls and tail then
                            numeric = bound_rhs_kind(
                                ls.rhs and ls.rhs[tail],
                                stored_model, feature_set) == "number"
                        end
                    end
                    if numeric then
                        for _, t in ipairs(arith_tokens(feature_set)) do
                            expected[#expected + 1] = t
                        end
                    end
                end
                -- under "cond" a variable-valued operand also continues
                -- into a conditioned term — "x ∧ B" -> "x ∧ B | C" — an
                -- outcome or number cannot be conditioned
                if feature_set and feature_set.cond then
                    local condable =
                        get_model_node_info(stored_model, token) ~= nil
                        or token:find("|", 1, true) ~= nil
                        or token:match("%)%s*$") ~= nil
                    if not condable and feature_set.let then
                        local ls = let_scope_at(formula, to_pos + 1)
                        for _, nm in ipairs(ls and ls.names or {}) do
                            if nm == token then
                                condable = true
                                break
                            end
                        end
                    end
                    if not condable then
                        local tail = token:match("([%a_][%w_]*)%s*$")
                        condable = tail ~= nil
                            and get_model_node_info(stored_model, tail)
                                ~= nil
                    end
                    if condable then
                        expected[#expected + 1] = "|"
                    end
                end
            else
                local sufs = completions()
                if #sufs > 0 then expected = sufs end
            end
        elseif token ~= "" then
            -- a flagged token that ends the input may just be incomplete:
            -- "Grade = L" -> "ow", "IDP(A,B | G" -> "rade"
            local sufs = completions()
            -- a trailing outcome name is "not a variable" yet still
            -- becomes a claim via a comparison: "Easy" -> "Easy =
            -- Difficulty" — offer the comparison operators too.
            if err.key == "not_a_variable" then
                for _, v in ipairs(get_model_outcomes(stored_model)) do
                    if v == token then
                        expected = {"=", "≤", "≥", "<", ">"}
                        break
                    end
                end
            end
            if #sufs > 0 then
                expected = expected or {}
                for _, s in ipairs(sufs) do expected[#expected + 1] = s end
            end
        end
        -- a trailing "LET" parses as a bare identifier and is flagged
        -- "not a variable" or "not boolean" — in the let's own slot it
        -- is the keyword opening a binding whose name comes next; the
        -- <name> marker opens the UI's letter keyboard
        if not expected and feature_set and feature_set.let then
            local ls = let_scope_at(formula, to_pos + 1)
            if ls and ls.expect == "name" then
                expected = {"<name>"}
            end
        end
    end
    return {method = "formula_report", ok = false,
            error = err.msg, key = err.key,
            from = from, ["to"] = to_pos, expected = expected,
            -- completions extend the flagged token: they splice in right
            -- behind it, not at its start
            ins_from = expected and to_pos and (to_pos + 1) or nil,
            ins_to = expected and to_pos and (to_pos + 1) or nil,
            seq = seq or 0}
end

local function eval_semantic_error(err, seq)
    local from, to_pos = pos_to_table(err.positional)
    return {method = "eval_result", ok = false,
            error = err.msg, key = err.key,
            from = from, ["to"] = to_pos,
            seq = seq or 0}
end

-- an arithmetic subtree with at least one identifier leaf is a
-- random-variable arithmetic term ("numvar"), not a scalar expression —
-- provided every leaf is a variable name or a number.  An identifier
-- inside P(…) or a comparison belongs to that subformula, so only
-- arithmetic nodes are transparent here.
-- lazy module proxies: the browser worker registers module sources into
-- package.preload only once a request handler asks for them, so a
-- main-chunk require would run before anything is fetchable — and
-- require_module would even cache that failure permanently.  Indexing
-- or calling the proxy defers the real require to first use, which
-- always happens inside a request (after the sources are registered).
local function lazy_module(name)
    local real
    local function get()
        if not real then real = assert(require_module(name)) end
        return real
    end
    return setmetatable({}, {
        __index = function(_, k) return get()[k] end,
        __call  = function(_, ...) return get()(...) end,
    })
end
local varterm = lazy_module("logic.varterm")
suggestions = lazy_module("logic.suggestions")
dist_family = lazy_module("logic.dist_family")
local compute_shared_order = lazy_module("model_checker.compute_shared_order")
local boolean_claim = lazy_module("model_checker.boolean_claim")

-- is `op` the operator name of a named distribution literal (the
-- "dists" feature)?  The name is the lowercase family key
local function is_pdist_op(op)
    return dist_family.specs[op] ~= nil
end

local function is_varterm_node(node)
    return varterm.is_varterm(node)
end

-- --------------------------------------------------------------------
-- annotation-driven suggestions
--
-- The grammar registers suggestion payloads on err.suggest at the
-- farthest failure position (see lpeg_util.suggestable/labeled and
-- lib.parsing_context).  logic.suggestions resolves them against the
-- model environment built here — this replaces the old text-scanning
-- position classifier + label-table expansion entirely.
-- --------------------------------------------------------------------

-- everything a payload category expands against: model names and
-- domains, numeric variables, LET-bound names in scope at `pos`, the
-- feature set.  `pos` is the byte position the suggestions are for.
function suggest_env(model, formula, pos, feature_set)
    local env = {
        model = model,
        formula = formula,
        pos = pos,
        nodes = get_model_names(model),
        all_outcomes = get_model_outcomes(model),
        outcomes_of = {},
        bound = {},
        features = feature_set,
    }
    local numeric_set = {}
    for _, n in ipairs(model and model.nodes or {}) do
        if type(n) == "table" and type(n.name) == "string" then
            local outs = {}
            for _, v in ipairs(n.outcomes or {}) do
                outs[#outs + 1] = tostring(v)
            end
            env.outcomes_of[n.name] = outs
            if node_is_numeric(n) then numeric_set[n.name] = true end
        end
    end
    env.numeric = function(nm) return numeric_set[nm] == true end
    env.is_var = function(nm)
        return get_model_node_info(model, nm) ~= nil
    end
    -- the domain of a variable-valued term NODE: a plain identifier
    -- resolves against the model, a conditional takes its left term's
    -- domain, and the literals resolve statically via varterm.domain
    local function node_domain(ast)
        if not ast or type(ast) ~= "table" then return nil end
        if ast.get_type and ast:get_type() == "identifier" then
            local si = get_model_node_info(model, ast:get_identifier())
            return si and si.outcomes or nil
        end
        if ast.get_type and ast:get_type() == "operator"
           and ast:get_operator_name() == "conditional" then
            return node_domain(ast:get_child(1))
        end
        local ok, dom = pcall(varterm.domain, ast)
        if ok then return dom end
        return nil
    end
    env.varterm_domain = node_domain
    -- LET-bound names visible at `pos` complete like model variables;
    -- a bound right side's kind ("number"/"boolq") decides the numeric
    -- slots, and a bound variable term supplies its source's domain
    if feature_set and feature_set.let and type(formula) == "string" then
        env.let_scope_at = function(p)
            return let_scope_at(formula, p)
        end
        local ls = let_scope_at(formula, pos)
        if ls then
            env.let_scope = {
                expect = ls.expect,
                names = ls.names or {},
                pending = ls.pending,
                assign_at = ls.assign_at,
                body_at = ls.body_at,
                rhs = ls.rhs,
            }
            env.bound = env.let_scope.names
            local kinds = {}
            for _, nm in ipairs(env.bound) do
                kinds[nm] = bound_rhs_kind(ls.rhs and ls.rhs[nm],
                                           model, feature_set)
                local dom = ls.rhs and ls.rhs[nm]
                    and varterm_source_domain
                    and varterm_source_domain(model, ls.rhs[nm], feature_set)
                if type(dom) == "table" then
                    local outs = {}
                    for _, v in ipairs(dom) do
                        outs[#outs + 1] = tostring(v)
                    end
                    env.outcomes_of[nm] = outs
                end
            end
            env.bound_kind = function(nm) return kinds[nm] end
        else
            env.bound_kind = function() return nil end
        end
    else
        env.let_scope_at = function() return nil end
        env.bound_kind = function() return nil end
    end
    return env
end

-- resolve a parse failure's annotation channel (expected labels +
-- suggest payloads + journal) to the ordered offer list; nil (and
-- stays nil) when the position offers nothing
function resolve_suggests(model, formula, pos, err, feature_set, splice_to)
    if type(err) ~= "table" then return nil end
    local env = suggest_env(model, formula, pos, feature_set)
    -- when the suggestion replaces a span [pos, splice_to) the
    -- resolver's word-boundary padding looks at the byte after the span
    env.splice_to = splice_to
    local toks = suggestions.resolve(err, env)
    if not toks or #toks == 0 then return nil end
    return toks, env
end

-- the parser's annotation channel at `pos` of `formula`: parse the text
-- up to pos; when the prefix is already a complete formula a sentinel
-- byte forces a failure at its end so the continuation annotations
-- surface.  Returns the error table (expected/suggest/order/notes) plus
-- the position the failure actually anchored at (earlier than `pos`
-- when the prefix itself has a gap).
function probe_suggests(parse, formula, pos, feature_set)
    local prefix = formula:sub(1, pos - 1)
    collectgarbage("stop")
    local ok, res = pcall(parse, prefix, feature_set)
    if ok then
        ok, res = pcall(parse, prefix .. "\1", feature_set)
    end
    collectgarbage("restart")
    if ok or type(res) ~= "table" then return nil end
    return res, res.positional and res.positional.from
end

-- the declared domain of a MUX selector or RENAME source term: a plain
-- name resolves against the model; a compound term is parsed — a
-- conditional takes its left term's domain ("MUX(X | C, …)" keys are
-- X's outcomes), DIST/RENAME/MUX literals resolve statically via
-- varterm.domain.  Returns nil when the domain cannot be determined
-- (numexpr, bound names, unresolvable literals).
varterm_source_domain = function(model, src, feature_set)
    local sname = src and src:match("^%s*([%a_][%w_]*)%s*$")
    if sname then
        local si = get_model_node_info(model, sname)
        return si and si.outcomes or nil
    end
    if not src or src:match("^%s*$") then return nil end
    local parse = get_parser()
    local ok, ast = pcall(parse, src, feature_set)
    if not ok or type(ast) ~= "table" then return nil end
    local function dom(nd)
        if nd:get_type() == "identifier" then
            local si = get_model_node_info(model, nd:get_identifier())
            return si and si.outcomes or nil
        end
        if nd:get_type() ~= "operator" then return nil end
        local opname = nd:get_operator_name()
        if opname == "conditional" then
            return dom(nd:get_child(1))
        end
        -- only the literal operators carry a statically known domain;
        -- a numexpr or claim-shaped source leaves it unresolved
        if opname == "dist" or opname == "rename" or opname == "mux"
           or dist_family.specs[opname] then
            local dok, d = pcall(varterm.domain, nd)
            return dok and d or nil
        end
        return nil
    end
    return dom(ast)
end

local function is_numexpr_node(node)
    if node:get_type() ~= "operator" then return false end
    if not arithmetic_operators[node:get_operator_name()] then return false end
    local has_var = false
    local function walk(nd)
        local t = nd:get_type()
        -- a DIST/RENAME literal is a variable leaf like an identifier
        if t == "identifier" or is_varterm_node(nd) then
            has_var = true
            return true
        end
        if t == "value" then return true end
        if t ~= "operator"
           or not arithmetic_operators[nd:get_operator_name()] then
            return false
        end
        for i = 1, nd:get_num_children() do
            if not walk(nd:get_child(i)) then return false end
        end
        return true
    end
    return walk(node) and has_var
end

local let_rhs_kind  -- forward: conditional_is_boolean recurses into a
                    -- let's body, let_rhs_kind classifies a conditional
                    -- right side
local let_denotes_variable  -- forward: a let's body decides whether
                            -- P(let) is a marginal query
local bound_entry   -- forward: defined with the LET scope helpers
                    -- below; conditional_is_boolean already resolves
                    -- bound names

-- run fn(let_body_node) with the let's sequential binding scope
-- installed on info.bound, then restore the caller's scope.  Binding
-- entries come from let_rhs_kind — best-effort when a right side is
-- malformed (validation reports the real error elsewhere).
local function with_let_scope(node, info, fn)
    local saved = info.bound
    local scope = {}
    if saved then
        for k, v in pairs(saved) do scope[k] = v end
    end
    info.bound = scope
    for i = 1, node:get_num_children() - 1 do
        local binding = node:get_child(i)
        if binding:get_type() == "operator"
           and binding:get_operator_name() == "binding" then
            local name_node = binding:get_child(1)
            if name_node and name_node:get_type() == "identifier" then
                scope[name_node:get_identifier()] =
                    let_rhs_kind(binding:get_child(2), info) or {}
            end
        end
    end
    local result = fn(node:get_child(node:get_num_children()))
    info.bound = saved
    return result
end

-- is a conditional AST "term | claim" a Boolean claim (a conditioned
-- event, usable wherever a formula is expected) or a random term (a
-- conditioned variable, which yields a distribution)?  Decided by the
-- left operand: a variable or arithmetic term makes a random term, a
-- claim an event.  A LET-bound name counts as a variable unless its
-- entry is marked Boolean (a bound claim).
local function conditional_is_boolean(ast, info)
    local left = ast:get_child(1)
    if left:get_type() == "identifier" then
        local b = bound_entry(info, left:get_identifier())
        return b ~= nil and b.boolean == true
    end
    if is_varterm_node(left) then return false end
    if is_numexpr_node(left) then return false end
    if left:get_type() == "operator" then
        local lop = left:get_operator_name()
        if lop == "conditional" then
            return conditional_is_boolean(left, info)
        end
        if lop == "let" then
            return with_let_scope(left, info, function(body)
                if body:get_type() == "identifier" then
                    local b = bound_entry(info, body:get_identifier())
                    return b ~= nil and b.boolean == true
                end
                if is_varterm_node(body) or is_numexpr_node(body) then
                    return false
                end
                if body:get_type() == "operator"
                   and body:get_operator_name() == "conditional" then
                    return conditional_is_boolean(body, info)
                end
                return true
            end)
        end
    end
    return true
end

local function is_conditional_node(node)
    return node:get_type() == "operator"
       and node:get_operator_name() == "conditional"
end

-- LET-binding scope helpers (feature "let"): info.bound maps a bound
-- source name to {boolean, domain_kind, values, outcomes, num_values} —
-- the same shape the model tables use so the identifier checks below
-- treat a bound name like a variable that happens to live in the
-- formula instead of the network.  `boolean` marks bindings to a claim
-- or Boolean query atom (usable where a Boolean operand is expected).
bound_entry = function(info, name)
    return info.bound and info.bound[name] or nil
end

-- a usable variable name in the current scope: a model variable or a
-- LET-bound one
local function known_variable(info, name)
    return info.variables[name] or bound_entry(info, name) ~= nil
end

-- the outcome-name set a name takes in scope (nil when unknown)
local function scope_values(info, name)
    local b = bound_entry(info, name)
    if b then return b.values end
    return info.var_values[name]
end

-- the ordered outcome list a name takes in scope (nil when unknown)
local function scope_outcomes(info, name)
    local b = bound_entry(info, name)
    if b then return b.outcomes end
    return info.var_outcomes[name]
end

-- a bare identifier denotes a Boolean claim when its domain is
-- Boolean-spelled ("GOAL_2" reads as "GOAL_2 = true" on andes-style
-- {false, true} domains — the same shorthand the solvers apply)
local function boolean_domain_var(info, name)
    local outcomes = scope_outcomes(info, name)
    return outcomes ~= nil
       and boolean_claim.is_boolean_domain(outcomes)
end

-- the real-valued outcome set a name takes in scope (nil when unknown)
local function scope_num_values(info, name)
    local b = bound_entry(info, name)
    if b then return b.num_values end
    return info.var_num_values[name]
end

-- "numeric"/"string"/nil for a variable in scope
local function scope_domain_kind(info, name)
    local b = bound_entry(info, name)
    if b then return b.domain_kind end
    if not info.variables[name] then return nil end
    return info.numeric_vars[name] and "numeric" or "string"
end

local function bool_bound_entry()
    return {boolean = true, domain_kind = "string",
            values = {F = true, T = true}, outcomes = {"F", "T"}}
end

-- is the support of a random-variable term statically decidable?
-- "numeric" when every declared outcome is a real number, "string" when
-- they are all names, nil when undecidable (mixed literal domains,
-- unresolved identifier/MUX branches) — the runtime evaluation decides
-- those.  A moment query (E/VAR/SD) rejects "string" operands up front.
local function moment_domain_kind(node, info)
    local t = node:get_type()
    if t == "identifier" then
        local name = node:get_identifier()
        return scope_domain_kind(info, name)
    end
    if t == "value" then return "numeric" end
    if t ~= "operator" then return nil end
    local op = node:get_operator_name()
    if op == "conditional" then
        -- a conditioned variable keeps its left term's support
        return moment_domain_kind(node:get_child(1), info)
    end
    if op == "let" then
        return with_let_scope(node, info, function(body)
            return moment_domain_kind(body, info)
        end)
    end
    if arithmetic_operators[op] then
        -- numeric iff every leaf is numeric: a string leaf poisons the
        -- whole expression, an undecidable one leaves it unknown
        local kind = "numeric"
        for i = 1, node:get_num_children() do
            local k = moment_domain_kind(node:get_child(i), info)
            if k == "string" then return "string" end
            if k ~= "numeric" then kind = nil end
        end
        return kind
    end
    -- a DIST/RENAME/MUX/FAMILY literal's static domain
    return varterm.domain_kind(node)
end

local validate_varterm, validate_property

-- every leaf of a numexpr must be a real-valued variable or a number
local function validate_numexpr(node, info)
    local t = node:get_type()
    if t == "identifier" then
        local name = node:get_identifier()
        if scope_domain_kind(info, name) == "numeric" then return nil end
        if known_variable(info, name) then
            return make_semantic_error("not_numeric_variable",
                node:get_positional(), {name = name})
        end
        return make_semantic_error("not_a_variable",
            node:get_positional(), {name = name})
    end
    if is_varterm_node(node) then
        -- a DIST/RENAME leaf must itself be well-formed and declare a
        -- numeric domain to participate in arithmetic
        local err = validate_varterm(node, info)
        if err then return err end
        if varterm.domain_kind(node) ~= "numeric" then
            return make_semantic_error("not_numeric_variable",
                node:get_positional(), {name = tostring(node)})
        end
        return nil
    end
    if t == "value" or t == "box" then return nil end
    if t ~= "operator" then
        return make_semantic_error("not_numeric", node:get_positional())
    end
    for i = 1, node:get_num_children() do
        local err = validate_numexpr(node:get_child(i), info)
        if err then return err end
    end
    return nil
end

-- DIST(o↦p,…)/RENAME(term,o↦o',…): semantic checks for the variable
-- literals.  Mirrors the solver-side validation so check_formula
-- reports the same problems early, with positions.
local DIST_TOL = 1e-6

-- the source outcomes a RENAME first argument or a MUX selector refers
-- to, when they are statically known: an identifier's declared domain,
-- a varterm's declared domain, a conditional's left domain.  numexpr
-- sources are computed at solve time and return nil here.
local rename_source_domain  -- forward: mux resolution recurses into it

-- quietly merge two ordered domains (MUX domain rule): numbers sort
-- numerically, strings interleave via compute_shared_order; returns nil
-- for mixed kinds or an ambiguous/conflicting order — the caller's own
-- validation reports the real error key
local function quiet_merge_domains(list_a, list_b)
    local kind = nil
    for _, list in ipairs({list_a, list_b}) do
        for _, v in ipairs(list) do
            local k = type(v) == "number" and "numeric" or "string"
            if kind and kind ~= k then
                return nil
            end
            kind = k
        end
    end
    if kind == "numeric" then
        local seen, out = {}, {}
        for _, list in ipairs({list_a, list_b}) do
            for _, v in ipairs(list) do
                if not seen[v] then
                    seen[v] = true
                    out[#out + 1] = v
                end
            end
        end
        table.sort(out)
        return out
    end
    local ok, merged = pcall(compute_shared_order, list_a, list_b)
    return ok and merged or nil
end

-- a MUX branch constant: a bare number is a point mass on that
-- outcome, an identifier naming no model variable is a point mass on
-- that outcome name (the contextual literal rule a comparison right
-- side uses).  Returns the outcome value or nil for variable terms.
local function mux_branch_const(branch, info)
    if branch:get_type() == "value" then
        return branch:get_value()
    end
    if branch:get_type() == "identifier"
       and not known_variable(info, branch:get_identifier()) then
        return branch:get_identifier()
    end
    return nil
end

-- fold the constant branch values into a merged variable-branch
-- domain: numbers and names append in entry order (deduplicated),
-- then a numeric result is resorted — the same order rule the
-- numeric domain merge uses.  `merged` is never mutated.  Returns
-- domain, kind — or nils + the offending node on a kind conflict.
local function mux_fold_consts(merged, kind, consts)
    local out, seen = {}, {}
    for _, v in ipairs(merged or {}) do
        seen[v] = true
        out[#out + 1] = v
    end
    for _, c in ipairs(consts) do
        local ck = type(c.value) == "number" and "numeric" or "string"
        if kind == nil then
            kind = ck
        elseif kind ~= ck then
            return nil, nil, c.node
        end
        if not seen[c.value] then
            seen[c.value] = true
            out[#out + 1] = c.value
        end
    end
    if kind == "numeric" then table.sort(out) end
    return out, kind
end

-- the domain kind of a resolved domain list — "numeric"/"string",
-- nil for an empty/unknown one (a merged list is never internally
-- mixed: the merge would have failed instead)
local function resolved_domain_kind(domain)
    if not domain or #domain == 0 then return nil end
    return type(domain[1]) == "number" and "numeric" or "string"
end

-- a MUX's output domain when every branch domain is resolvable
local function mux_resolved_domain(node, info)
    local merged, consts = nil, {}
    for _, branch in ipairs(varterm.mux_branches(node)) do
        local c = mux_branch_const(branch, info)
        if c ~= nil then
            consts[#consts + 1] = {value = c, node = branch}
        else
            local bd = rename_source_domain(branch, info)
            if not bd then
                return nil
            end
            merged = merged and quiet_merge_domains(merged, bd) or bd
            if not merged then
                return nil
            end
        end
    end
    local out = mux_fold_consts(merged, resolved_domain_kind(merged),
                              consts)
    return out
end

rename_source_domain = function(source, info)
    local t = source:get_type()
    if t == "identifier" then
        local name = source:get_identifier()
        local b = bound_entry(info, name)
        if b then return b.outcomes, name end
        return info.var_outcomes[name], name
    end
    if is_varterm_node(source) then
        if source:get_operator_name() == "mux" then
            return mux_resolved_domain(source, info), tostring(source)
        end
        return varterm.domain(source), tostring(source)
    end
    if t == "operator" and source:get_operator_name() == "conditional" then
        return rename_source_domain(source:get_child(1), info)
    end
    if t == "operator" and source:get_operator_name() == "let" then
        -- a let's source domain is its body's, under the let's scope
        return with_let_scope(source, info, function(body)
            return rename_source_domain(body, info)
        end)
    end
    return nil, tostring(source)
end

-- "numeric"/"string"/nil (unknown): the domain kind a variable term
-- resolves to, consulting the model for identifiers and recursing
-- through conditionals and MUX branches
local function term_domain_kind(node, info)
    local t = node:get_type()
    if t == "identifier" then
        return scope_domain_kind(info, node:get_identifier())
    end
    if is_varterm_node(node) then
        if node:get_operator_name() == "mux" then
            local kind = nil
            for _, branch in ipairs(varterm.mux_branches(node)) do
                local c = mux_branch_const(branch, info)
                local bk = c ~= nil
                           and (type(c) == "number" and "numeric"
                                or "string")
                           or term_domain_kind(branch, info)
                if bk == nil then
                    return nil
                end
                if kind and kind ~= bk then
                    return nil  -- mixed: the mux's own validation reports it
                end
                kind = bk
            end
            return kind
        end
        if is_pdist_op(node:get_operator_name()) then
            local k = varterm.domain_kind(node)
            if k then return k end
            -- a LET-bound argument leaves the support undecidable, but
            -- the domain kind is still static: every family is numeric
            -- except DEGENERATE's name form, which follows the bound
            -- name's kind
            if node:get_operator_name() == "degenerate" then
                local a = node:get_child(1)
                if a and a:get_type() == "identifier" then
                    local b = bound_entry(info, a:get_identifier())
                    if b then return b.domain_kind end
                end
            end
            return "numeric"
        end
        return varterm.domain_kind(node)
    end
    if t == "operator" and node:get_operator_name() == "conditional" then
        return term_domain_kind(node:get_child(1), info)
    end
    if t == "operator" and node:get_operator_name() == "let" then
        return with_let_scope(node, info, function(body)
            return term_domain_kind(body, info)
        end)
    end
    if is_numexpr_node(node) then
        return "numeric"
    end
    return nil
end

validate_varterm = function(node, info)
    local op = node:get_operator_name()
    -- boxes inside the map entries would surface as "not a value"
    -- instead of "incomplete", so scan them first
    local function scan_boxes(nd)
        for i = 1, nd:get_num_children() do
            local c = nd:get_child(i)
            if c:get_type() == "box" then
                return c
            end
            if c:get_type() == "operator" then
                local b = scan_boxes(c)
                if b then return b end
            end
        end
        return nil
    end
    if op == "dist" then
        for i = 1, node:get_num_children() do
            local b = scan_boxes(node:get_child(i))
            if b then
                return make_semantic_error("incomplete_formula", b:get_positional())
            end
        end
        local seen = {}
        local numeric = nil
        local sum = 0
        for i = 1, node:get_num_children() do
            local entry = node:get_child(i)
            local key_node = entry:get_child(1)
            local weight_node = entry:get_child(2)
            local key = varterm.leaf_literal(key_node)
            local knum = type(key) == "number"
            if numeric == nil then
                numeric = knum
            elseif numeric ~= knum then
                return make_semantic_error("dist_mixed_domain",
                    key_node:get_positional())
            end
            if knum and not (info.features and info.features.numval) then
                return make_semantic_error("numval_required",
                    key_node:get_positional())
            end
            if seen[key] then
                return make_semantic_error("duplicate_value",
                    key_node:get_positional(),
                    {variable = tostring(node), value = tostring(key)})
            end
            seen[key] = true
            local p = weight_node:get_type() == "value"
                      and weight_node:get_value() or nil
            if type(p) ~= "number" or p ~= p
               or p == math.huge or p == -math.huge
               or p < 0 or p > 1 then
                return make_semantic_error("dist_bad_probability",
                    weight_node:get_positional(),
                    {value = tostring(weight_node)})
            end
            sum = sum + p
        end
        if math.abs(sum - 1) > DIST_TOL then
            return make_semantic_error("dist_not_normalized",
                node:get_positional(), {sum = tostring(sum)})
        end
        return nil
    end

    -- a named distribution literal FAMILY(arg, …): arity and parameter
    -- kinds come from logic/dist_family.lua; a □ argument reports
    -- "incomplete" rather than a bad value
    local pdist = dist_family.specs[op]
    if pdist then
        for i = 1, node:get_num_children() do
            if node:get_child(i):get_type() == "box" then
                return make_semantic_error("incomplete_formula",
                    node:get_child(i):get_positional())
            end
        end
        local args = {}
        local masked = nil
        for i = 1, node:get_num_children() do
            local a = node:get_child(i)
            args[i] = varterm.leaf_literal(a)
            if a:get_type() == "identifier" then
                -- a LET-bound name stands for its bound value: a
                -- point-mass binding's single outcome is the literal
                -- the parameter expects; a bound scalar whose value
                -- is decided at evaluation is masked (the solver's
                -- check_args validates it then)
                local b = bound_entry(info, a:get_identifier())
                if b and b.outcomes and #b.outcomes == 1 then
                    args[i] = b.outcomes[1]
                elseif b and b.domain_kind == "numeric" then
                    args[i] = 0
                    masked = masked or {}
                    masked[i] = true
                end
            end
        end
        local errkey, errparams = dist_family.check_args(pdist, args,
                                                         masked)
        if errkey then
            local pos = node:get_positional()
            if errparams and errparams.argi then
                local c = node:get_child(errparams.argi)
                pos = c and c:get_positional() or pos
            end
            return make_semantic_error(errkey, pos, errparams)
        end
        return nil
    end

    if op == "mux" then
        local b = scan_boxes(node)
        if b then
            return make_semantic_error("incomplete_formula", b:get_positional())
        end
        -- a MUX argument that claims to be a variable term gets the
        -- same checks a RENAME source gets
        local function check_term(term)
            local terr
            if term:get_type() == "identifier" then
                if not known_variable(info, term:get_identifier()) then
                    terr = make_semantic_error("not_a_variable",
                        term:get_positional(),
                        {name = term:get_identifier()})
                end
            elseif is_varterm_node(term) then
                terr = validate_varterm(term, info)
            elseif is_numexpr_node(term) then
                terr = validate_numexpr(term, info)
            elseif term:get_type() == "operator"
                   and (term:get_operator_name() == "conditional"
                        or term:get_operator_name() == "let") then
                terr = validate_property(term, "any", info)
            end
            return terr
        end
        -- a branch may also be a constant: a bare number (numeric
        -- outcome, needs "numval" downstream) or an identifier naming
        -- no model variable (a literal outcome name).  Everything else
        -- still has to be a variable term.
        local function is_branch(term)
            return varterm.is_variable_term(term)
                   or term:get_type() == "value"
        end
        local function check_branch(term)
            if mux_branch_const(term, info) ~= nil then return nil end
            return check_term(term)
        end
        local mixture = varterm.mux_is_mixture(node)
        if mixture then
            -- every child is a "branch ↦ real" entry
            local sum = 0
            for i = 1, node:get_num_children() do
                local entry = node:get_child(i)
                if entry:get_type() ~= "operator"
                   or entry:get_operator_name() ~= "equal" then
                    return make_semantic_error("mux_bad_entry",
                        entry:get_positional())
                end
                local branch = entry:get_child(1)
                local weight_node = entry:get_child(2)
                if not is_branch(branch) then
                    return make_semantic_error("mux_branch_not_variable",
                        branch:get_positional())
                end
                local terr = check_branch(branch)
                if terr then return terr end
                local p = weight_node and weight_node:get_type() == "value"
                          and weight_node:get_value() or nil
                if type(p) ~= "number" or p ~= p
                   or p == math.huge or p == -math.huge
                   or p < 0 or p > 1 then
                    return make_semantic_error("dist_bad_probability",
                        weight_node:get_positional(),
                        {value = tostring(weight_node)})
                end
                sum = sum + p
            end
            if node:get_num_children() < 1 then
                return make_semantic_error("mux_bad_entry",
                    node:get_positional())
            end
            if math.abs(sum - 1) > DIST_TOL then
                return make_semantic_error("dist_not_normalized",
                    node:get_positional(), {sum = tostring(sum)})
            end
        else
            -- selector form: source term + "outcome ↦ branch" entries
            if node:get_num_children() < 2 then
                return make_semantic_error("mux_bad_entry",
                    node:get_positional())
            end
            local source = node:get_child(1)
            if not varterm.is_variable_term(source) then
                return make_semantic_error("mux_source_not_variable",
                    source:get_positional())
            end
            local serr = check_term(source)
            if serr then return serr end
            local sel_domain = rename_source_domain(source, info)
            local sel_set = {}
            for _, v in ipairs(sel_domain or {}) do
                sel_set[v] = true
            end
            local seen_key = {}
            for i = 2, node:get_num_children() do
                local entry = node:get_child(i)
                if entry:get_type() ~= "operator"
                   or entry:get_operator_name() ~= "equal" then
                    return make_semantic_error("mux_bad_entry",
                        entry:get_positional())
                end
                local key_node = entry:get_child(1)
                local branch = entry:get_child(2)
                local key = varterm.leaf_literal(key_node)
                if key == nil then
                    return make_semantic_error("mux_bad_entry",
                        entry:get_positional())
                end
                if sel_domain and not sel_set[key] then
                    return make_semantic_error("invalid_value_for",
                        key_node:get_positional(),
                        {value = tostring(key), variable = tostring(source)})
                end
                if seen_key[key] then
                    return make_semantic_error("duplicate_value",
                        key_node:get_positional(),
                        {variable = tostring(node), value = tostring(key)})
                end
                seen_key[key] = true
                if not is_branch(branch) then
                    return make_semantic_error("mux_branch_not_variable",
                        branch:get_positional())
                end
                local terr = check_branch(branch)
                if terr then return terr end
            end
            if sel_domain then
                for _, v in ipairs(sel_domain) do
                    if not seen_key[v] then
                        return make_semantic_error("mux_missing_outcome",
                            node:get_positional(),
                            {value = tostring(v), variable = tostring(source)})
                    end
                end
            end
        end
        -- shared domain check: variable branch kinds must agree and
        -- the merged order must be unambiguous when all domains are
        -- resolvable; constants then fold in positionally (numbers
        -- resort the domain, names append in entry order), a kind
        -- conflict is mux_mixed_domain
        local kind = nil
        local merged = nil
        local consts = {}
        for _, branch in ipairs(varterm.mux_branches(node)) do
            local c = mux_branch_const(branch, info)
            if c ~= nil then
                consts[#consts + 1] = {value = c, node = branch}
            else
                local bk = term_domain_kind(branch, info)
                if bk ~= nil then
                    if kind == nil then
                        kind = bk
                    elseif kind ~= bk then
                        return make_semantic_error("mux_mixed_domain",
                            branch:get_positional())
                    end
                end
                local bd = rename_source_domain(branch, info)
                if bd ~= nil then
                    if merged == nil then
                        merged = bd
                    elseif kind == "numeric" then
                        merged = quiet_merge_domains(merged, bd)
                    elseif kind == "string" then
                        local ok2, m = pcall(compute_shared_order,
                                             merged, bd)
                        if not ok2 then
                            local k2 = tostring(m):find("conflict", 1,
                                                      true)
                                       and "mux_conflicting_domain"
                                       or "mux_ambiguous_domain"
                            return make_semantic_error(k2,
                                branch:get_positional())
                        end
                        merged = m
                    end
                end
            end
        end
        local _, fkind, cerr = mux_fold_consts(merged, kind, consts)
        if cerr then
            return make_semantic_error("mux_mixed_domain",
                cerr:get_positional())
        end
        kind = fkind or kind
        if kind == "numeric"
           and not (info.features and info.features.numval) then
            return make_semantic_error("numval_required",
                node:get_positional())
        end
        return nil
    end

    -- op == "rename": first the source term, then the map entries
    local b = scan_boxes(node)
    if b then
        return make_semantic_error("incomplete_formula", b:get_positional())
    end
    local source = node:get_child(1)
    if not varterm.is_variable_term(source) then
        return make_semantic_error("rename_source_not_variable",
            source:get_positional())
    end
    local src_domain, src_name = rename_source_domain(source, info)
    -- validate the source itself
    local serr
    if source:get_type() == "identifier" then
        if not known_variable(info, source:get_identifier()) then
            serr = make_semantic_error("not_a_variable",
                source:get_positional(), {name = source:get_identifier()})
        end
    elseif is_varterm_node(source) then
        serr = validate_varterm(source, info)
    elseif is_numexpr_node(source) then
        serr = validate_numexpr(source, info)
    elseif source:get_type() == "operator"
           and source:get_operator_name() == "conditional" then
        serr = validate_property(source, "any", info)
    end
    if serr then return serr end
    local src_set = {}
    for _, v in ipairs(src_domain or {}) do
        src_set[v] = true
    end
    local seen_key = {}
    local out_seen = {}
    local out_domain = {}
    local out_numeric = nil
    local covered = 0
    for i = 2, node:get_num_children() do
        local entry = node:get_child(i)
        local key_node = entry:get_child(1)
        local new_node = entry:get_child(2)
        local key = varterm.leaf_literal(key_node)
        local new = varterm.leaf_literal(new_node)
        if src_domain and not src_set[key] then
            return make_semantic_error("invalid_value_for",
                key_node:get_positional(),
                {value = tostring(key), variable = src_name})
        end
        if seen_key[key] then
            return make_semantic_error("duplicate_value",
                key_node:get_positional(),
                {variable = tostring(node), value = tostring(key)})
        end
        seen_key[key] = true
        covered = covered + 1
        local nnum = type(new) == "number"
        if out_numeric == nil then
            out_numeric = nnum
        elseif out_numeric ~= nnum then
            return make_semantic_error("rename_mixed_domain",
                new_node:get_positional())
        end
        if nnum and not (info.features and info.features.numval) then
            return make_semantic_error("numval_required",
                new_node:get_positional())
        end
        if out_seen[new] and out_domain[#out_domain] ~= new then
            return make_semantic_error("rename_nonadjacent",
                new_node:get_positional(), {value = tostring(new)})
        end
        if not out_seen[new] then
            out_seen[new] = true
            out_domain[#out_domain + 1] = new
        end
    end
    if src_domain and covered < #src_domain then
        for _, v in ipairs(src_domain) do
            if not seen_key[v] then
                return make_semantic_error("rename_missing_outcome",
                    node:get_positional(),
                    {value = tostring(v), variable = src_name})
            end
        end
    end
    return nil
end

-- classify a LET binding's right side into the bound-entry shape the
-- scope helpers return (feature "let"): a claim/Boolean query becomes a
-- Boolean entry ({F,T}), a scalar a numeric point mass, a variable
-- term the domain it declares.  nil = the right side denotes nothing
-- bindable (a MAP/MPE assignment table cannot be a variable).
let_rhs_kind = function(rhs, info)
    local t = rhs:get_type()
    if t == "identifier" then
        local name = rhs:get_identifier()
        local b = bound_entry(info, name)
        if b then return b end
        if info.variables[name] then
            return {domain_kind = info.numeric_vars[name]
                                 and "numeric" or "string",
                    values = info.var_values[name],
                    outcomes = info.var_outcomes[name],
                    num_values = info.var_num_values[name]}
        end
        -- a name denoting no variable is a literal outcome name and
        -- binds a point mass on it (the contextual-literal rule a
        -- MUX branch uses)
        return {domain_kind = "string",
                values = {[name] = true},
                outcomes = {name}}
    end
    if t == "value" then
        local v = rhs:get_value()
        return {domain_kind = "numeric",
                values = {[tostring(v)] = true},
                outcomes = {v},
                num_values = {[v] = true}}
    end
    if t ~= "operator" then return nil end
    local op = rhs:get_operator_name()
    if op == "binding" then return nil end
    if op == "let" then
        -- a nested let's value is its body's — classify under the
        -- scope the inner bindings add
        return with_let_scope(rhs, info, function(body)
            return let_rhs_kind(body, info)
        end)
    end
    if op == "modify_probability" then
        return let_rhs_kind(rhs:get_child(1), info)
    end
    if is_conditional_node(rhs) then
        if conditional_is_boolean(rhs, info) then
            return bool_bound_entry()
        end
        return {domain_kind = term_domain_kind(rhs:get_child(1), info)}
    end
    if is_varterm_node(rhs) then
        local dom
        if op == "mux" then
            dom = mux_resolved_domain(rhs, info)
        else
            dom = varterm.domain(rhs)
        end
        local kind = term_domain_kind(rhs, info)
        local values, num_values
        if dom then
            values = {}
            num_values = {}
            for _, v in ipairs(dom) do
                values[tostring(v)] = true
                if type(v) == "number" then
                    num_values[v] = true
                end
            end
        end
        return {domain_kind = kind, values = values,
                outcomes = dom, num_values = num_values}
    end
    if is_numexpr_node(rhs) then
        return {domain_kind = "numeric"}
    end
    if compare_operators[op] or logical_operators[op]
       or op == "map" or op == "mpe" or op == "idp" or op == "infl" then
        -- a claim, a Boolean combination or a Boolean query result
        return bool_bound_entry()
    end
    if op == "prob" then
        -- P(X)/P(X|c) under "marginal" yields the queried variable's
        -- distribution — the bound variable copies its domain; any
        -- other P(φ) is a scalar probability and binds a point mass
        local child1 = rhs:get_child_or_nil(1)
        if child1 then
            local marginal = false
            if child1:get_type() == "identifier" then
                marginal = info.features ~= nil
                           and info.features.marginal == true
                           and known_variable(info, child1:get_identifier())
            elseif is_varterm_node(child1) or is_numexpr_node(child1)
                   or (is_conditional_node(child1)
                       and not conditional_is_boolean(child1, info))
                   or (child1:get_type() == "operator"
                       and child1:get_operator_name() == "let"
                       and let_denotes_variable(child1, info)) then
                marginal = true
            end
            if marginal then
                return {domain_kind = term_domain_kind(child1, info)}
            end
        end
        return {domain_kind = "numeric"}
    end
    if MOMENT_OPS[op] or arithmetic_operators[op] then
        -- a scalar number binds a point-mass variable
        return {domain_kind = "numeric"}
    end
    return nil
end

-- does a LET term denote a random variable (true) or a Boolean claim /
-- scalar (false)?  Decided by the body under the let's own scope —
-- P(LET X = e IN X) is a marginal query while LET B = φ IN B binds a
-- Boolean atom
let_denotes_variable = function(node, info)
    return with_let_scope(node, info, function(body)
        local t = body:get_type()
        if t == "identifier" then
            local b = bound_entry(info, body:get_identifier())
            -- a bound claim denotes a Boolean atom — P of it is the
            -- scalar probability, not a marginal; any other bound or
            -- model name is a variable
            if b then return not b.boolean end
            return info.variables[body:get_identifier()] ~= nil
        end
        if is_varterm_node(body) or is_numexpr_node(body) then
            return true
        end
        if is_conditional_node(body) then
            return not conditional_is_boolean(body, info)
        end
        if t == "operator" and body:get_operator_name() == "let" then
            return let_denotes_variable(body, info)
        end
        return false
    end)
end

validate_property = function(property, expected, info)
    local t = property:get_type()
    if t == "box" then
        -- a □ placeholder parses everywhere but makes the formula
        -- incomplete: it can never be model checked
        return make_semantic_error("incomplete_formula", property:get_positional())
    end
    if t == "operator" then
        -- MAP/IDP/INFL check their argument NAME LISTS, not the child
        -- nodes — a box in such a slot would surface as "not a variable"
        -- instead of "incomplete", so flag direct box children first
        for i = 1, property:get_num_children() do
            local ch = property:get_child(i)
            if ch and ch:get_type() == "box" then
                return make_semantic_error("incomplete_formula", ch:get_positional())
            end
        end
    end
    if t == "identifier" then
        local name = property:get_identifier()
        if expected == "variable" or expected == "any" then
            -- a standalone name is a formula only when it names a
            -- variable — a model one or a LET-bound one (its marginal
            -- distribution is the query result)
            if not known_variable(info, name) then
                return make_semantic_error("not_a_variable", property:get_positional(), {name = name})
            end
        elseif expected == "variable_or_value" then
            if not (known_variable(info, name) or info.all_values[name]) then
                return make_semantic_error("unknown_identifier", property:get_positional(), {name = name})
            end
        elseif expected == "boolean" then
            -- a LET-bound claim is a Boolean operand; a bare model
            -- variable is one when its domain is Boolean-spelled
            -- ("GOAL_2" reads as "GOAL_2 = true")
            local b = bound_entry(info, name)
            if not (b and b.boolean) and not boolean_domain_var(info, name) then
                return make_semantic_error("not_boolean", property:get_positional())
            end
        elseif expected == "numeric" then
            return make_semantic_error("not_numeric", property:get_positional())
        end
        return nil
    elseif t == "value" then
        local v = property:get_value()
        if expected == "numeric" then
            if type(v) ~= "number" then
                return make_semantic_error("not_numeric", property:get_positional())
            end
            return nil
        end
        if expected == "variable_or_value" then
            if not info.all_values[tostring(v)] then
                return make_semantic_error("not_a_value", property:get_positional(), {value = v})
            end
            return nil
        end
        if expected == "boolean" then
            return make_semantic_error("not_boolean", property:get_positional())
        end
        return nil
    elseif t == "operator" then
        local op = property:get_operator_name()
        if op == "let" then
            -- LET name = rhs (; name = rhs)* IN body (feature "let"):
            -- sequential per-formula bindings.  The scope lives in
            -- info.bound — a fresh map shadowing the enclosing one while
            -- the let's bindings and body are validated, so nothing
            -- leaks into a sibling subformula.
            if not (info.features and info.features.let) then
                return make_semantic_error("unknown_operator", property:get_positional())
            end
            local n = property:get_num_children()
            local saved_bound = info.bound
            local scope = {}
            if saved_bound then
                for k, v in pairs(saved_bound) do
                    scope[k] = v
                end
            end
            info.bound = scope
            for i = 1, n - 1 do
                local binding = property:get_child(i)
                local name_node = binding:get_child(1)
                local rhs = binding:get_child(2)
                if name_node:get_type() ~= "identifier" then
                    -- a "LET □ = e IN …" placeholder — the name slot
                    -- needs an identifier
                    info.bound = saved_bound
                    return make_semantic_error("incomplete_formula",
                        name_node:get_positional())
                end
                local name = name_node:get_identifier()
                if info.variables[name] or scope[name] then
                    info.bound = saved_bound
                    return make_semantic_error("let_redefines",
                        name_node:get_positional(), {name = name})
                end
                local err
                if rhs:get_type() == "identifier"
                   and not known_variable(info, rhs:get_identifier())
                   then
                    -- a literal outcome name binds a point mass (the
                    -- contextual-literal rule) — the variable check
                    -- does not apply
                    err = nil
                else
                    err = validate_property(rhs, "any", info)
                end
                if err then
                    info.bound = saved_bound
                    return err
                end
                local kind = let_rhs_kind(rhs, info)
                if not kind then
                    info.bound = saved_bound
                    return make_semantic_error("let_rhs",
                        rhs:get_positional(), {name = name})
                end
                scope[name] = kind
            end
            -- the body inherits the caller's expected kind — a Boolean
            -- formula, a scalar term or an intervention context
            local err = validate_property(property:get_child(n), expected, info)
            info.bound = saved_bound
            return err
        elseif op == "prob" then
            if expected ~= "any" and expected ~= "numeric" then
                return make_semantic_error("not_numeric", property:get_positional())
            end
            local n = property:get_num_children()
            if n < 1 then
                return make_semantic_error("not_boolean", property:get_positional())
            end
            local child1 = property:get_child(1)
            if child1:get_type() == "operator" then
                local cop = child1:get_operator_name()
                if cop == "prob" then
                    return make_semantic_error("prob_nested", child1:get_positional(), {quantifier = "P"})
                end
            end
            -- the "marginal" feature admits a random-variable query:
            -- P(X) returns X's distribution, P(X | B) its conditional
            -- marginal.  A conditional random term X|C (the "cond"
            -- feature) is a marginal query as well.
            local marginal_query = false
            if child1:get_type() == "identifier" then
                local name = child1:get_identifier()
                local b = bound_entry(info, name)
                if b and b.boolean then
                    -- a LET-bound claim is a Boolean atom: P(B) is the
                    -- scalar probability like P(φ), no marginal query
                elseif info.features and info.features.marginal then
                    if not known_variable(info, name) then
                        return make_semantic_error("not_a_variable", child1:get_positional(),
                                                   {name = name})
                    end
                    marginal_query = true
                elseif boolean_domain_var(info, name) then
                    -- a bare Boolean-domain variable is the claim
                    -- "X = <truthy outcome>": P(GOAL_2) is P(GOAL_2 =
                    -- true) — the child validates as "boolean" below
                else
                    return make_semantic_error("not_boolean", child1:get_positional())
                end
            elseif is_conditional_node(child1) and not conditional_is_boolean(child1, info) then
                marginal_query = true
            elseif is_numexpr_node(child1) or is_varterm_node(child1) then
                -- "numvar"/"dist"/"rename": P(X − Y), P(DIST(…)),
                -- P(RENAME(…)) query the variable's (conditional)
                -- marginal
                marginal_query = true
            elseif child1:get_type() == "operator"
                   and child1:get_operator_name() == "let"
                   and let_denotes_variable(child1, info) then
                -- "let": P(LET X = e IN X) queries the bound
                -- variable's marginal, like a varterm
                marginal_query = true
            end
            if child1:get_type() == "value" then
                return make_semantic_error("not_boolean", child1:get_positional())
            end
            -- a marginal query yields a distribution, not a number
            if marginal_query and expected == "numeric" then
                return make_semantic_error("not_numeric", property:get_positional())
            end
            for i = 1, n do
                local child = property:get_child(i)
                local is_modify = child:get_type() == "operator" and child:get_operator_name() == "modify_probability"
                if is_modify then
                    local err = validate_property(child, "model", info)
                    if err then return err end
                elseif i == 1 and (is_conditional_node(child)
                                   or is_numexpr_node(child)
                                   or is_varterm_node(child)
                                   or (child:get_type() == "operator"
                                       and child:get_operator_name() == "let"
                                       and marginal_query)) then
                    -- a conditional term queries a claim's conditional
                    -- probability or a variable's conditional marginal;
                    -- numexpr/varterm/variable-let children query the
                    -- variable's marginal
                    local err = validate_property(child, "any", info)
                    if err then return err end
                elseif i == 1 and marginal_query then
                    -- the identifier was already checked above
                else
                    local err = validate_property(child, "boolean", info)
                    if err then return err end
                end
            end
            return nil
        elseif MOMENT_OPS[op] then
            -- E(term)/VAR(term)/SD(term): a scalar moment of a random
            -- variable — the operand must be a variable-valued term
            -- (a model variable, a conditioned variable, a variable
            -- literal or a numeric expression), never a claim
            if expected ~= "any" and expected ~= "numeric" then
                return make_semantic_error("not_numeric", property:get_positional())
            end
            local operand = property:get_child_or_nil(1)
            if not operand then
                return make_semantic_error("not_a_variable", property:get_positional())
            end
            -- recurse first: a literal's own errors and an identifier's
            -- existence surface before the operand-shape complaint
            local err = validate_property(operand, "any", info)
            if err then return err end
            local ot = operand:get_type()
            local is_term = ot == "identifier" or is_varterm_node(operand)
                or is_numexpr_node(operand)
                or (is_conditional_node(operand)
                    and not conditional_is_boolean(operand, info))
            if not is_term then
                return make_semantic_error("not_a_variable",
                    operand:get_positional(), {name = tostring(operand)})
            end
            -- a moment needs a real-valued support — reject the cases
            -- where the operand's domain is statically known to be all
            -- outcome names; undecidable domains defer to evaluation
            if moment_domain_kind(operand, info) == "string" then
                return make_semantic_error("not_numeric_variable",
                    operand:get_positional(), {name = tostring(operand)})
            end
            return nil
        elseif op == "map" or op == "mpe" then
            if expected ~= "any" and expected ~= "boolean" then
                return make_semantic_error("quantifier_not_allowed", property:get_positional(), {quantifier = op})
            end
            local cond = nil
            if op == "map" then
                local opobj = property:get_operator()
                local idlist = opobj.identifier_list or {}
                for _, name in ipairs(idlist) do
                    if not known_variable(info, name) then
                        return make_semantic_error("map_query_not_variable", property:get_positional(), {name = name})
                    end
                end
                local n = property:get_num_children()
                if opobj.has_condition or n > #idlist then
                    cond = property:get_child_or_nil(n)
                end
            else
                cond = property:get_child_or_nil(1)
            end
            if cond then
                if cond:get_type() == "identifier" and cond:get_identifier() == "true" then
                    return nil
                end
                local err = validate_property(cond, "boolean", info)
                if err then return err end
            end
            return nil
        elseif op == "idp" or op == "infl" then
            if expected ~= "any" and expected ~= "boolean" then
                return make_semantic_error("not_boolean", property:get_positional())
            end
            local opdef = property:get_operator()
            local key = (op == "idp") and "idp_var_not_variable" or "infl_var_not_variable"
            for _, name in ipairs({opdef.left, opdef.right}) do
                if not known_variable(info, name) then
                    return make_semantic_error(key, property:get_positional(), {name = name})
                end
            end
            for _, name in ipairs(opdef.cond or {}) do
                if not known_variable(info, name) then
                    return make_semantic_error(key, property:get_positional(), {name = name})
                end
            end
            return nil
        elseif op == "modify_probability" then
            if expected ~= "any" and expected ~= "model"
               and expected ~= "numeric" and expected ~= "boolean" then
                return make_semantic_error("not_numeric", property:get_positional())
            end
            local opdef = property:get_operator()
            -- entry children (the "outcome = prob" and "var = value"
            -- clauses) are not recursed into — scan them for box holes
            -- so "[Grade: □ = 0.5]" reports incomplete, not a bad value
            for i = 1, property:get_num_children() do
                local ch = property:get_child(i)
                if ch and ch:get_type() == "operator" then
                    for j = 1, ch:get_num_children() do
                        local gc = ch:get_child(j)
                        if gc and gc:get_type() == "box" then
                            return make_semantic_error("incomplete_formula", gc:get_positional())
                        end
                    end
                end
            end
            local target = opdef.identifier
            if not known_variable(info, target) then
                return make_semantic_error("modify_target_not_variable", property:get_positional(), {name = target})
            end
            local tvalues = scope_values(info, target) or {}
            for val, _ in pairs(opdef.prob_map or {}) do
                if not tvalues[tostring(val)] then
                    return make_semantic_error("invalid_value_for", property:get_positional(), {value = val, variable = target})
                end
            end
            for var, val in pairs(opdef.condition or {}) do
                if not known_variable(info, var) then
                    return make_semantic_error("not_a_variable", property:get_positional(), {name = var})
                end
                local vs = scope_values(info, var) or {}
                if not vs[tostring(val)] and not known_variable(info, tostring(val)) then
                    return make_semantic_error("invalid_value_for", property:get_positional(), {value = val, variable = var})
                end
            end
            local inner = property:get_child_or_nil(1)
            if inner then
                local inner_expected
                if expected == "any" then
                    inner_expected = "any"
                elseif expected == "numeric" then
                    inner_expected = "numeric"
                else
                    -- "model" (intervention inside P(...)) or "boolean"
                    inner_expected = "boolean"
                end
                local err = validate_property(inner, inner_expected, info)
                if err then return err end
            end
            return nil
        elseif op == "dist" or op == "rename" or op == "mux"
               or is_pdist_op(op) then
            -- "dist"/"rename"/"mux"/a named distribution: a variable
            -- literal — a valid "any" formula (its marginal is the
            -- result) but neither a Boolean claim nor a scalar
            if expected == "boolean" or expected == "model" then
                return make_semantic_error("not_boolean", property:get_positional())
            end
            if expected ~= "any" then
                return make_semantic_error("not_numeric", property:get_positional())
            end
            return validate_varterm(property, info)
        elseif logical_operators[op] then
            if expected ~= "any" and expected ~= "boolean" then
                return make_semantic_error("not_boolean", property:get_positional())
            end
            for i = 1, property:get_num_children() do
                local err = validate_property(property:get_child(i), "boolean", info)
                if err then return err end
            end
            return nil
        elseif op == "conditional" then
            -- "term | claim" (the "cond" feature): a conditioned
            -- variable yields a distribution, a conditioned claim is
            -- Boolean
            if not info.features or not info.features.cond then
                return make_semantic_error("unknown_operator", property:get_positional())
            end
            local boolean_term = conditional_is_boolean(property, info)
            if expected ~= "any" and expected ~= "boolean" then
                -- a conditioned claim is not numeric and a conditioned
                -- variable is neither numeric nor a model
                return make_semantic_error("not_numeric", property:get_positional())
            elseif expected == "boolean" and not boolean_term then
                return make_semantic_error("not_boolean", property:get_positional())
            end
            local left = property:get_child(1)
            if left:get_type() == "value"
               or (left:get_type() == "operator"
                   and left:get_operator_name() == "prob")
               or (left:get_type() == "operator"
                   and arithmetic_operators[left:get_operator_name()]
                   and not is_numexpr_node(left)) then
                -- a scalar (number, P(...), constant arithmetic) cannot
                -- be conditioned; a random-variable arithmetic term can
                return make_semantic_error("not_boolean", left:get_positional())
            end
            local err = validate_property(left, "any", info)
            if err then return err end
            for i = 2, property:get_num_children() do
                local err = validate_property(property:get_child(i), "boolean", info)
                if err then return err end
            end
            return nil
        elseif compare_operators[op] then
            if expected ~= "any" and expected ~= "boolean" then
                return make_semantic_error("not_boolean", property:get_positional())
            end
            local c1, c2 = property:get_child(1), property:get_child(2)
            if c1:get_type() == "identifier" and c2:get_type() == "identifier" then
                local n1, n2 = c1:get_identifier(), c2:get_identifier()
                local v1 = known_variable(info, n1)
                local v2 = known_variable(info, n2)
                if not (v1 or v2) then
                    return make_semantic_error("comparison_no_variable", property:get_positional())
                end
                if not v1 then
                    if not (scope_values(info, n2) or {})[n1] then
                        return make_semantic_error("invalid_value_for", c1:get_positional(), {value = n1, variable = n2})
                    end
                elseif not v2 then
                    if not (scope_values(info, n1) or {})[n2] then
                        return make_semantic_error("invalid_value_for", c2:get_positional(), {value = n2, variable = n1})
                    end
                else
                    -- two variables: under "numval" a real-valued
                    -- variable compares numerically with another
                    -- real-valued variable — outcome sets need not
                    -- interleave — but never with a string-valued one
                    local k1 = scope_domain_kind(info, n1)
                    local k2 = scope_domain_kind(info, n2)
                    if info.features and info.features.numval
                       and (k1 == "numeric" or k2 == "numeric") then
                        if not (k1 == "numeric" and k2 == "numeric") then
                            return make_semantic_error("comparison_incomparable", property:get_positional(), {left = n1, right = n2})
                        end
                        return nil
                    end
                    local shared = false
                    local vals1 = scope_values(info, n1) or {}
                    local vals2 = scope_values(info, n2) or {}
                    for sv, _ in pairs(vals1) do
                        if vals2[sv] then
                            shared = true
                            break
                        end
                    end
                    if not shared and next(vals1) and next(vals2) then
                        return make_semantic_error("comparison_incomparable", property:get_positional(), {left = n1, right = n2})
                    end
                end
                return nil
            else
                -- "(X|C) = x" compares a conditioned variable against
                -- an outcome of its domain
                local ci = nil
                for i = 1, property:get_num_children() do
                    if is_conditional_node(property:get_child(i)) then
                        ci = i
                        break
                    end
                end
                if ci then
                    local cnode = property:get_child(ci)
                    local other = property:get_child(3 - ci)
                    local oname = other:get_type() == "identifier" and other:get_identifier() or nil
                    if conditional_is_boolean(cnode, info) then
                        -- a conditioned event compares against a truth
                        -- outcome: "(φ | C) = T" is the claim φ|C itself
                        local err = validate_property(cnode, "boolean", info)
                        if err then return err end
                        if oname ~= "F" and oname ~= "T" then
                            return make_semantic_error("not_a_value", other:get_positional(),
                                                       {value = oname or "?"})
                        end
                        return nil
                    end
                    -- a conditioned variable compares against an outcome
                    -- of its domain: "(X | C) = x"
                    local err = validate_property(cnode, "any", info)
                    if err then return err end
                    local x = cnode:get_child(1)
                    while x:get_type() == "operator" do x = x:get_child(1) end
                    local xname = x:get_type() == "identifier" and x:get_identifier() or nil
                    if is_numexpr_node(other) then
                        -- "(X|C) > (Y−Z)": the conditioned variable must
                        -- be real-valued, the arithmetic term well-formed
                        if not (xname and scope_domain_kind(info, xname) == "numeric") then
                            return make_semantic_error("not_numeric_variable",
                                cnode:get_child(1):get_positional(), {name = xname or "?"})
                        end
                        local nerr = validate_numexpr(other, info)
                        if nerr then return nerr end
                        return nil
                    end
                    if other:get_type() == "value" then
                        -- "(X|C) = 0.5" / "(X|C) < 0.5": a real literal
                        -- compares against a real-valued conditioned
                        -- variable; equality requires an actual outcome
                        if not (xname and scope_domain_kind(info, xname) == "numeric") then
                            return make_semantic_error("invalid_value_for", other:get_positional(),
                                {value = tostring(other:get_value()), variable = xname or "?"})
                        end
                        if property:get_operator_name() == "equal"
                           and not (scope_num_values(info, xname) or {})[other:get_value()] then
                            return make_semantic_error("invalid_value_for", other:get_positional(),
                                {value = tostring(other:get_value()), variable = xname})
                        end
                        return nil
                    end
                    if oname and bound_entry(info, oname) then
                        -- a bound name is a variable, not an outcome
                        -- literal: the conditioned variable and it must
                        -- be comparable — equal domain kinds, or a
                        -- shared outcome when both are statically known
                        local xk = scope_domain_kind(info, xname)
                        local ok = scope_domain_kind(info, oname)
                        if xk and ok and xk ~= ok then
                            return make_semantic_error("comparison_incomparable",
                                property:get_positional(),
                                {left = xname, right = oname})
                        end
                        local xv = scope_values(info, xname)
                        local ov = scope_values(info, oname)
                        if xv and ov then
                            local shared = false
                            for sv, _ in pairs(ov) do
                                if xv[sv] then shared = true break end
                            end
                            if not shared then
                                return make_semantic_error("comparison_incomparable",
                                    property:get_positional(),
                                    {left = xname, right = oname})
                            end
                        end
                        return nil
                    end
                    if not (xname and oname and scope_values(info, xname)
                            and scope_values(info, xname)[oname]) then
                        return make_semantic_error("invalid_value_for", other:get_positional(),
                                                   {value = oname or "?", variable = xname})
                    end
                    return nil
                end
                -- a DIST/RENAME literal operand: validate the literal
                -- itself, then classify the other side against its
                -- declared domain (mirrors the variable rules: a
                -- numeric side forces numeric semantics, two string
                -- domains need a shared outcome name)
                local vi = nil
                for i = 1, property:get_num_children() do
                    if is_varterm_node(property:get_child(i)) then
                        vi = i
                        break
                    end
                end
                if vi then
                    local vnode = property:get_child(vi)
                    local err = validate_varterm(vnode, info)
                    if err then return err end
                    -- a MUX operand's domain/kind resolve through the
                    -- model (identifier branches), DIST/RENAME declare
                    -- theirs statically
                    local function resolved_domain(nd)
                        if nd:get_operator_name() == "mux" then
                            return mux_resolved_domain(nd, info)
                        end
                        return varterm.domain(nd)
                    end
                    local vnum = term_domain_kind(vnode, info) == "numeric"
                    -- nil = undecidable (a LET-bound argument): the
                    -- kind still classifies, membership checks defer
                    -- to evaluation
                    local vdom = resolved_domain(vnode)
                    local other = property:get_child(3 - vi)
                    local function incomparable()
                        return make_semantic_error("comparison_incomparable",
                            property:get_positional(),
                            {left = tostring(property:get_child(1)),
                             right = tostring(property:get_child(2))})
                    end
                    if is_varterm_node(other) then
                        err = validate_varterm(other, info)
                        if err then return err end
                        local onum = term_domain_kind(other, info) == "numeric"
                        if onum ~= vnum then
                            return incomparable()
                        end
                        if not vnum and vdom then
                            local oset = {}
                            for _, v in ipairs(resolved_domain(other) or {}) do
                                oset[v] = true
                            end
                            local shared = false
                            for _, v in ipairs(vdom) do
                                if oset[v] then shared = true break end
                            end
                            if not shared then return incomparable() end
                        end
                        return nil
                    end
                    if is_numexpr_node(other) then
                        local nerr = validate_numexpr(other, info)
                        if nerr then return nerr end
                        if not vnum then return incomparable() end
                        return nil
                    end
                    if other:get_type() == "value" then
                        if not vnum then return incomparable() end
                        if property:get_operator_name() == "equal"
                           and vdom then
                            local found = false
                            for _, v in ipairs(vdom) do
                                if v == other:get_value() then found = true break end
                            end
                            if not found then
                                return make_semantic_error("invalid_value_for",
                                    other:get_positional(),
                                    {value = tostring(other:get_value()),
                                     variable = tostring(vnode)})
                            end
                        end
                        return nil
                    end
                    if other:get_type() == "identifier" then
                        local oname = other:get_identifier()
                        if not known_variable(info, oname) then
                            -- an outcome literal must be in the
                            -- literal's declared domain
                            local inset = false
                            for _, v in ipairs(vdom or {}) do
                                if v == oname then inset = true break end
                            end
                            if vdom and not inset then
                                return make_semantic_error("invalid_value_for",
                                    other:get_positional(),
                                    {value = oname, variable = tostring(vnode)})
                            end
                            return nil
                        end
                        local onum = scope_domain_kind(info, oname) == "numeric"
                        if onum ~= vnum then return incomparable() end
                        if not vnum and vdom then
                            local shared = false
                            local ovals = scope_values(info, oname)
                            for _, v in ipairs(vdom) do
                                if ovals and ovals[tostring(v)] then
                                    shared = true
                                    break
                                end
                            end
                            if not shared and ovals then
                                return incomparable()
                            end
                        end
                        return nil
                    end
                    if is_conditional_node(other) then
                        return validate_property(other, "any", info)
                    end
                    return validate_property(other, "numeric", info)
                end
                -- numeric comparisons: a real literal or a numexpr
                -- operand against a real-valued variable
                local numeric_cmp = false
                for i = 1, property:get_num_children() do
                    local c = property:get_child(i)
                    if c:get_type() == "value" or is_numexpr_node(c) then
                        numeric_cmp = true
                    end
                end
                if numeric_cmp then
                    for i = 1, property:get_num_children() do
                        local c = property:get_child(i)
                        if is_numexpr_node(c) then
                            local err = validate_numexpr(c, info)
                            if err then return err end
                        elseif c:get_type() == "identifier" then
                            local n = c:get_identifier()
                            if not known_variable(info, n) then
                                return make_semantic_error("comparison_no_variable", c:get_positional())
                            end
                            if scope_domain_kind(info, n) ~= "numeric" then
                                return make_semantic_error("not_numeric_variable", c:get_positional(), {name = n})
                            end
                        elseif c:get_type() ~= "value" then
                            local err = validate_property(c, "numeric", info)
                            if err then return err end
                        end
                    end
                    -- "X = 0.5" needs the literal to be an outcome of X
                    if property:get_operator_name() == "equal" then
                        for i = 1, property:get_num_children() do
                            local c = property:get_child(i)
                            local o = property:get_child(property:get_num_children() - i + 1)
                            if c:get_type() == "value" and o:get_type() == "identifier" then
                                local n = o:get_identifier()
                                if scope_domain_kind(info, n) == "numeric"
                                   and not (scope_num_values(info, n) or {})[c:get_value()] then
                                    return make_semantic_error("invalid_value_for", c:get_positional(),
                                        {value = tostring(c:get_value()), variable = n})
                                end
                            end
                        end
                    end
                    return nil
                end
                for i = 1, property:get_num_children() do
                    local err = validate_property(property:get_child(i), "numeric", info)
                    if err then return err end
                end
                return nil
            end
        elseif arithmetic_operators[op] then
            if is_numexpr_node(property) then
                -- "numvar": arithmetic over random variables denotes a
                -- derived variable (a distribution term), so it is a
                -- valid "any" formula but neither a Boolean claim nor a
                -- scalar number
                if expected == "boolean" then
                    return make_semantic_error("not_boolean", property:get_positional())
                end
                if expected ~= "any" then
                    return make_semantic_error("not_numeric", property:get_positional())
                end
                return validate_numexpr(property, info)
            end
            if expected ~= "any" and expected ~= "numeric" then
                return make_semantic_error("not_numeric", property:get_positional())
            end
            for i = 1, property:get_num_children() do
                local err = validate_property(property:get_child(i), "numeric", info)
                if err then return err end
            end
            return nil
        end
        return nil
    end
    return nil
end

-- The identifier/number token the caret (a 1-based "insert before this
-- byte" position) sits inside or at the start of, as a half-open byte
-- range [from, to).  Returns nil outside such a token — only names and
-- numbers are replaceable; operators and punctuation are pure insert
-- positions.
local function token_span_at(text, caret)
    local i, n = 1, #text
    while i <= n do
        local b = text:byte(i)
        local j, ident
        if b < 128 and ((b >= 65 and b <= 90) or (b >= 97 and b <= 122)
                        or b == 95) then
            ident = true
            j = i + 1
            while j <= n do
                local c = text:byte(j)
                if c < 128 and ((c >= 65 and c <= 90)
                                or (c >= 97 and c <= 122)
                                or (c >= 48 and c <= 57) or c == 95) then
                    j = j + 1
                else break end
            end
        elseif b >= 48 and b <= 57 then
            ident = true
            j = i + 1
            while j <= n do
                local c = text:byte(j)
                if (c >= 48 and c <= 57) or c == 46 then j = j + 1
                else break end
            end
        else
            j = i + (b < 128 and 1 or b < 224 and 2 or b < 240 and 3 or 4)
        end
        if caret >= i and caret < j then
            if ident then return i, j end
            return nil
        end
        i = j
    end
    return nil
end

-- Keep only the suggestion tokens that do not strand the text behind the
-- insertion point: tok is dropped when prefix..tok..suffix fails at its
-- very end with expected_eof (the inserted text is complete and the
-- suffix is trailing junk — "P(A=b" + ")" + ")" ).  A valid parse or an
-- open expectation (an operand still wanted) keeps the token: the gap it
-- leaves is fixable by continuing.
local function rescuing_tokens(parse, formula, ins_from, ins_to, toks, feature_set)
    local prefix = formula:sub(1, ins_from - 1)
    local suffix = formula:sub(ins_to)
    local out = nil
    for _, tok in ipairs(toks) do
        collectgarbage("stop")
        local ok, res = pcall(parse, prefix .. tok .. suffix, feature_set)
        collectgarbage("restart")
        local keep = ok
        if not keep and type(res) == "table" and res.expected then
            keep = true
            local labs = res.expected
            if type(labs) == "string" then labs = {labs} end
            for _, l in ipairs(labs) do
                if l == "expected_eof" then keep = false break end
            end
        end
        if keep then
            out = out or {}
            out[#out + 1] = tok
        end
    end
    return out
end

-- Suggestions for a text cursor inside a syntactically complete formula.
-- The formula is cut at the caret and the prefix's expectation set is
-- reused for the cut position; when the caret sits inside a name/number
-- token the cut goes to the token's start so a tapped suggestion
-- REPLACES it ("yes" -> "no" without deleting first).  Returns the
-- expected list plus the half-open byte splice range [from, to) the
-- client should insert into, or nil when the position offers nothing.
local function caret_expected(model, formula, caret, parse, feature_set)
    local ins_from, ins_to = caret, caret
    local ts, te = token_span_at(formula, caret)
    if ts then ins_from, ins_to = ts, te end
    local prefix = formula:sub(1, ins_from - 1)
    collectgarbage("stop")
    local ok, res = pcall(parse, prefix, feature_set)
    collectgarbage("restart")
    if ok then
        -- the caret sits right after a complete subformula: its own
        -- continuation set, filtered against the surviving suffix
        local env = suggest_env(model, formula, ins_from, feature_set)
        local ex = suggestions.continuations(res, env)
        if ex then
            ex = rescuing_tokens(parse, formula, ins_from, ins_to, ex,
                                 feature_set)
            if ex and #ex > 0 then return ex, ins_from, ins_to end
        end
        return nil
    end
    if type(res) == "table" then
        local efrom = res.positional and res.positional.from
        if efrom and efrom <= #prefix then
            -- the gap is earlier than the caret — fill the first gap
            ins_from, ins_to = efrom, efrom
        end
        local ex = resolve_suggests(model, formula, ins_from, res,
                                    feature_set, ins_to)
        if ex then
            ex = rescuing_tokens(parse, formula, ins_from, ins_to, ex,
                                 feature_set)
            if ex and #ex > 0 then return ex, ins_from, ins_to end
        end
    end
    return nil
end

-- ---------------------------------------------------------------------
-- "nodeformula": a node editor mode in which a node's CPT is defined by
-- a BayesL formula over the node's parents instead of a hand-filled
-- table.  The service resolves the formula to concrete rows: it must be
-- a variable term (identifier, DIST/RENAME/MUX literal, numexpr) or a
-- Boolean claim (materialised {F,T}); every identifier that names a
-- model variable must be one of the node's declared parents — the CPT
-- is a function of the conditioning set, nothing else may leak in.
-- Resolution fixes the parents at each row's values with point-mass
-- CPTs and evaluates P(formula): a varterm yields its marginal table, a
-- claim its probability of holding.  The formula's own domain becomes
-- the node's outcome list.

local NF_FORBIDDEN = {
    prob = true, map = true, mpe = true, idp = true, infl = true,
    modify_probability = true, conditional = true,
    expect = true, variance = true, sd = true,
}
local NF_BOOL_OPS = {
    ["not"] = true, ["and"] = true, nand = true, ["or"] = true,
    nor = true, implication = true, biimplication = true, xor = true,
}
local NF_CMP_OPS = {
    less = true, less_or_equal = true, equal = true,
    greater_or_equal = true, greater = true,
}

-- collect the variable references of a node formula; every identifier
-- naming a model variable must be a parent of the edited node, and
-- identifiers in variable positions must name variables at all.
-- Outcome literals (comparison right sides, DIST/RENAME/MUX map keys)
-- are free.  Returns nil or a semantic-error table.
local function nf_walk_vars(nd, info, parent_set, vars, node_name)
    local t = nd:get_type()
    if t == "identifier" then
        local name = nd:get_identifier()
        if bound_entry(info, name) then
            return nil   -- a bound name is an aux variable, not a parent
        end
        if not info.variables[name] then
            return make_semantic_error("not_a_variable",
                nd:get_positional(), {name = name})
        end
        if not parent_set[name] then
            return make_semantic_error("node_formula_nonparent",
                nd:get_positional(), {name = name, node = node_name})
        end
        vars[name] = true
        return nil
    end
    if t ~= "operator" then return nil end
    local op = nd:get_operator_name()
    if NF_FORBIDDEN[op] then
        return make_semantic_error("node_formula_construct",
            nd:get_positional(), {construct = op})
    end
    if op == "let" then
        -- sequential bindings like validate_property's let branch:
        -- each RHS is walked in the scope built so far (it may use
        -- parents), then the name enters scope for the next binding
        local n = nd:get_num_children()
        local saved_bound = info.bound
        local scope = {}
        if saved_bound then
            for k, v in pairs(saved_bound) do scope[k] = v end
        end
        info.bound = scope
        for i = 1, n - 1 do
            local binding = nd:get_child(i)
            local name_node = binding:get_child(1)
            if name_node:get_type() ~= "identifier" then
                info.bound = saved_bound
                return make_semantic_error("incomplete_formula",
                    name_node:get_positional())
            end
            local name = name_node:get_identifier()
            if info.variables[name] or scope[name] then
                info.bound = saved_bound
                return make_semantic_error("let_redefines",
                    binding:get_child(1):get_positional(), {name = name})
            end
            local e = nf_walk_vars(binding:get_child(2), info,
                                   parent_set, vars, node_name)
            if e then
                info.bound = saved_bound
                return e
            end
            scope[name] = let_rhs_kind(binding:get_child(2), info)
                          or "string"
        end
        local e = nf_walk_vars(nd:get_child(n), info, parent_set, vars,
                               node_name)
        info.bound = saved_bound
        return e
    end
    if op == "dist" then
        return nil   -- map keys are outcome literals, values weights
    elseif is_pdist_op(op) then
        return nil   -- FAMILY(...) arguments are literals, never vars
    elseif op == "rename" then
        return nf_walk_vars(nd:get_child(1), info, parent_set, vars,
                            node_name)
    elseif op == "mux" then
        -- a branch constant (a bare number, or an identifier naming no
        -- model variable) is an outcome literal, not a variable
        -- reference; the selector is always a term
        local function branch_vars(b)
            if b == nil or mux_branch_const(b, info) ~= nil then
                return nil
            end
            return nf_walk_vars(b, info, parent_set, vars, node_name)
        end
        local function entry_child(i, k)
            local e = nd:get_child(i)
            if e and e:get_type() == "operator"
               and e:get_operator_name() == "equal" then
                return e:get_child(k)
            end
            return nil
        end
        if varterm.mux_is_mixture(nd) then
            for i = 1, nd:get_num_children() do
                local e = branch_vars(entry_child(i, 1))
                if e then return e end
            end
        else
            local e = nf_walk_vars(nd:get_child(1), info, parent_set,
                                   vars, node_name)
            if e then return e end
            for i = 2, nd:get_num_children() do
                e = branch_vars(entry_child(i, 2))
                if e then return e end
            end
        end
        return nil
    elseif NF_CMP_OPS[op] then
        -- a side that is an identifier naming a model variable is a
        -- variable use; other identifiers are outcome literals
        for i = 1, nd:get_num_children() do
            local c = nd:get_child(i)
            if c:get_type() == "identifier" then
                local name = c:get_identifier()
                if info.variables[name] then
                    if not parent_set[name] then
                        return make_semantic_error(
                            "node_formula_nonparent", c:get_positional(),
                            {name = name, node = node_name})
                    end
                    vars[name] = true
                end
            else
                local e = nf_walk_vars(c, info, parent_set, vars,
                                       node_name)
                if e then return e end
            end
        end
        return nil
    end
    -- boolean connectives, arithmetic, and anything else: identifier
    -- children are variable references
    for i = 1, nd:get_num_children() do
        local e = nf_walk_vars(nd:get_child(i), info, parent_set, vars,
                               node_name)
        if e then return e end
    end
    return nil
end

local function handle(msg, hooks)
    local method = msg.method
    if method == "ping" then
        return {method = "pong", payload = msg.payload}
    elseif method == "eval" then
        local chunk = assert(load(msg.code or "", "eval"))
        local res = {pcall(chunk)}
        if not res[1] then error(res[2]) end
        table.remove(res, 1)
        return {method = "eval_result", result = res}
    elseif method == "get_model" then
        return {method = "model",
                model = stored_model or json.null,
                key = stored_model_key or json.null}
    elseif method == "list_example_models" then
        if EXAMPLES then
            local models = {}
            for i, name in ipairs(EXAMPLES.order) do
                local em = EXAMPLES.models[name]
                if em then
                    models[i] = {name = name, key = em.key}
                end
            end
            return {method = "example_model_list", models = models}
        else
            return {method = "example_model_list", models = {}}
        end
    elseif method == "load_example_model" then
        local key = msg.name
        if not (EXAMPLES and key) then
            return {method = "error", reason = "unknown example model"}
        end
        local found, found_key
        for _, m in pairs(EXAMPLES.models) do
            if m.key == key or _ == key then
                found = m.model
                found_key = m.key
                break
            end
        end
        if not found then
            return {method = "error", reason = "unknown example model: " .. tostring(key)}
        end
        -- copy before coercing: EXAMPLES keeps its declared outcomes
        local copy = {nodes = {}, edges = found.edges}
        for i, n in ipairs(found.nodes or {}) do
            local c = {}
            for k, v in pairs(n) do c[k] = v end
            copy.nodes[i] = c
        end
        found = copy
        coerce_numeric_outcomes(found, msg_features(msg))
        stored_model = found
        stored_model_key = found_key
        if hooks and hooks.save then
            hooks.save(json.encode(stored_model))
        end
        return {method = "example_model", model = found,
                key = found_key,
                problems = validate_model(found, msg_features(msg))}
    elseif method == "list_example_formulas" then
        local key = msg.model_key
        if not (EXAMPLES and key) then
            return {method = "example_formula_list", formulas = {}}
        end
        return {method = "example_formula_list",
                formulas = EXAMPLES.formulas[key] or {}}
    elseif method == "set_model" then
        if type(msg.model) ~= "table" then
            error("set_model needs a model object")
        end
        coerce_numeric_outcomes(msg.model, msg_features(msg))
        stored_model = msg.model
        stored_model_key = find_example_key(stored_model)
        if hooks and hooks.save then
            hooks.save(json.encode(stored_model))
        end
        -- collect as many problems as possible — the client marks every
        -- reported node/cell, not just the first
        return {method = "report",
                problems = validate_model(stored_model, msg_features(msg))}
    elseif method == "restore_model" then
        if type(msg.model) == "table" and msg.model ~= json.null then
            coerce_numeric_outcomes(msg.model, msg_features(msg))
            stored_model = msg.model
            stored_model_key = find_example_key(stored_model)
        end
        return {method = "report",
                problems = stored_model and validate_model(stored_model,
                                                           msg_features(msg))
                         or {}}
    elseif method == "check_formula" then
        if type(msg.formula) ~= "string" then
            return {method = "formula_report", ok = false,
                    error = "missing formula", seq = msg.seq or 0}
        end
        local formula = msg.formula
        local feature_set = msg_features(msg)
        -- a model restored before the client sent features still holds
        -- numeric-looking string outcomes — coerce on first use too
        coerce_numeric_outcomes(stored_model, feature_set)
        if formula == "" then
            -- An empty formula is not an error; it is simply a prompt for
            -- the valid opening tokens.  The client uses the `expected`
            -- list for the suggestion bar and leaves the status line empty.
            -- The list is resolved from the grammar's suggest payloads
            -- registered by parsing the empty string (phi+psi starter
            -- categories — <number> included via the psi number slot).
            local parse = get_parser()
            local payloads = probe_suggests(parse, formula, 1,
                                            feature_set)
            local exp = resolve_suggests(stored_model, formula, 1,
                                         payloads, feature_set)
            return {method = "formula_report", ok = false,
                    from = 1, ["to"] = 1,
                    input_len = 0,
                    expected = exp,
                    ins_from = 1, ins_to = 1,
                    seq = msg.seq or 0}
        end
        local parse = get_parser()
        collectgarbage("stop")
        local ok, res = pcall(parse, formula, feature_set)
        collectgarbage("restart")
        if ok then
            local ast = res
            local bn = get_cached_bn()
            local explanation = nil
            local segments = nil
            if bn then
                local info = collect_bn_info(bn, feature_set)
                local err = validate_property(ast, "any", info)
                if err then
                    -- The AST exists (a keyed error means the formula
                    -- parsed), so the English description can still be
                    -- generated — e.g. a formula with □ placeholders reads
                    -- as "... and □" while the box waits for input.
                    local rep = semantic_error_to_report(err, msg.seq,
                                                         formula, feature_set)
                    if rep.expected == nil then
                        -- the flagged span needs manual fixing, but the
                        -- caret may sit at a different spot that CAN be
                        -- filled — or inside the flagged token itself, in
                        -- which case a tap replaces it
                        local cur = tonumber(msg.cursor)
                        if cur and cur >= 1 and cur <= #formula then
                            local ex, f, t = caret_expected(stored_model,
                                                          formula, cur, parse,
                                                          feature_set)
                            if ex then
                                rep.expected = ex
                                rep.ins_from, rep.ins_to = f, t
                            end
                        end
                    end
                    local ex = get_explainer()
                    if ex then
                        local aok, ann = pcall(ex.explain_segments, ast, info)
                        if aok and ann then
                            rep.explanation = ann.text
                            rep.explanation_segments = ann.segments
                        end
                    end
                    return rep
                end
                local ex = get_explainer()
                if ex then
                    local ann = ex.explain_segments(ast, info)
                    explanation = ann and ann.text or nil
                    segments = ann and ann.segments or nil
                end
            else
                local ex = get_explainer()
                if ex then
                    local ann = ex.explain_segments(ast, nil)
                    explanation = ann and ann.text or nil
                    segments = ann and ann.segments or nil
                end
            end
            -- The suggestion set follows the text cursor: inside the
            -- formula the caret's own expected tokens apply (a token the
            -- caret touches is REPLACED by the tap), at the end the usual
            -- whole-formula continuations.  ins_from/ins_to tell the
            -- client which half-open byte range a tapped token splices
            -- into — the caret's token, the caret itself, or the end.
            local expected, ins_from, ins_to
            local cur = tonumber(msg.cursor)
            if cur and cur >= 1 and cur <= #formula then
                expected, ins_from, ins_to =
                    caret_expected(stored_model, formula, cur, parse,
                                   feature_set)
            end
            if not expected then
                -- no caret (or the caret path found nothing): the
                -- continuations after the complete formula — the AST
                -- itself decides which operators may follow
                local env = suggest_env(stored_model, formula,
                                        #formula + 1, feature_set)
                expected = suggestions.continuations(ast, env)
                ins_from, ins_to = #formula + 1, #formula + 1
            end
            return {method = "formula_report", ok = true,
                    explanation = explanation,
                    explanation_segments = segments,
                    expected = expected,
                    ins_from = ins_from, ins_to = ins_to,
                    seq = msg.seq or 0}
        else
            local err = res
            local from, to_pos, text, line, column, input_len, expected, msg_error
            local ins_from, ins_to
            if type(res) == "table" then
                if res.positional then
                    from = res.positional.from
                    to_pos = res.positional.to
                    text = res.positional.text
                    input_len = #(res.positional.input)
                    line, column = res.positional:get_from_line_column()
                end
                -- A failure position inside the text is a gap the user can
                -- still fill — suggestions splice in AT the error
                -- position, they are no longer append-only.  Candidates
                -- that would strand the suffix behind the gap are dropped.
                if from and res.expected then
                    -- in a let's binding tail the token at the error
                    -- position may be "IN" being typed — complete it
                    -- behind the token rather than inserting before it
                    local labs = res.expected
                    if type(labs) == "string" then labs = {labs} end
                    local let_tail = false
                    for _, l in ipairs(labs) do
                        if l == "expected_let_tail" then
                            let_tail = true
                            break
                        end
                    end
                    if let_tail then
                        local ts, te = token_span_at(formula, from)
                        if ts == from then
                            local tok = formula:sub(ts, te - 1)
                            if ts > 1 and formula:sub(ts - 1, ts - 1)
                                      :match("[%a%d_]") then
                                -- "5IN"/"5IN5"/"5I": the keyword lost
                                -- its leading boundary to the preceding
                                -- word — every insertion before it
                                -- strands the token, so the only sound
                                -- repair splices a separated " IN "
                                -- over the IN part
                                local n = tok:sub(1, 2) == "IN" and 2
                                          or tok:sub(1, 1) == "I"
                                          and 1 or 0
                                if n > 0 then
                                    expected = {" IN "}
                                    ins_from, ins_to = ts, ts + n
                                end
                            elseif #tok < 2
                               and ("IN"):sub(1, #tok) == tok then
                                expected = {("IN"):sub(#tok + 1)}
                                ins_from, ins_to = te, te
                            end
                        end
                    end
                    if not expected then
                        -- the labels+payloads+journal at `from` name the
                        -- slot — the resolver turns them into the
                        -- model-aware list; a token ending at the gap is
                        -- a partial being typed
                        local toks = resolve_suggests(stored_model,
                                                    formula, from, res,
                                                    feature_set)
                        if toks and #toks > 0 then
                            expected = rescuing_tokens(parse, formula,
                                                       from, from, toks,
                                                       feature_set)
                        end
                    end
                    local function placeholder_only(t)
                        for _, tok in ipairs(t or {}) do
                            local s = tostring(tok)
                            if s:sub(1, 1) ~= "<" or s:sub(-1, -1) ~= ">" then
                                return false
                            end
                        end
                        return true
                    end
                    if (not expected or #expected == 0
                        or placeholder_only(expected)) then
                        -- inserting before the offending byte rescues
                        -- nothing — but the byte may start a token a
                        -- suggestion can REPLACE ("Grade = 0.5" offers
                        -- the outcome list for the number's slot)
                        local ts, te = token_span_at(formula, from)
                        if ts == from then
                            local ex = resolve_suggests(stored_model,
                                                      formula, from,
                                                      res,
                                                      feature_set, te)
                            ex = ex and rescuing_tokens(parse, formula,
                                                        from, te, ex,
                                                        feature_set)
                            if ex and #ex > 0
                               and not placeholder_only(ex) then
                                expected, ins_from, ins_to = ex, from, te
                            end
                        end
                    end
                    if expected and #expected > 0 and not ins_from then
                        ins_from, ins_to = from, from
                    end
                    if expected and #expected == 0 then
                        expected = nil
                    end
                end
                if res.key == "parsing_error" then
                    -- The parser failure is already communicated through the
                    -- `expected` token list and the red underline; no need
                    -- for a generic "parsing error" string in the status line.
                    msg_error = nil
                else
                    msg_error = res.key or tostring(res)
                end
            else
                msg_error = tostring(res)
            end
            return {method = "formula_report", ok = false,
                    error = msg_error, from = from, ["to"] = to_pos,
                    text = text, line = line, column = column,
                    input_len = input_len, expected = expected,
                    ins_from = ins_from, ins_to = ins_to,
                    seq = msg.seq or 0}
        end
    elseif method == "get_tree" then
        if type(msg.formula) ~= "string" or msg.formula == "" then
            return {method = "tree_report", ok = false,
                    error = "no formula", seq = msg.seq or 0}
        end
        local parse = get_parser()
        collectgarbage("stop")
        local ok, ast = pcall(parse, msg.formula, msg_features(msg))
        collectgarbage("restart")
        if not ok then
            local from, to_pos, msg_error
            if type(ast) == "table" and ast.positional then
                from = ast.positional.from
                to_pos = ast.positional.to
            end
            return {method = "tree_report", ok = false,
                    error = msg_error or "parse error",
                    from = from, ["to"] = to_pos, seq = msg.seq or 0}
        end
        local ok2, layout = pcall(function()
            local tree = require "logic.tree_layout"
            -- identifier vocabularies let the client colour outcome
            -- names as enum literals vs variable names (LET-bound names
            -- are collected inside the layout walk itself)
            local names
            if stored_model and type(stored_model.nodes) == "table" then
                names = {vars = {}, vals = {}}
                for _, nd in ipairs(stored_model.nodes) do
                    names.vars[tostring(nd.name or "")] = true
                    for _, ov in ipairs(nd.outcomes or {}) do
                        names.vals[tostring(ov)] = true
                    end
                end
            end
            return tree.layout(ast, names)
        end)
        if not ok2 then
            return {method = "tree_report", ok = false,
                    error = tostring(layout), seq = msg.seq or 0}
        end
        return {method = "tree_report", ok = true,
                tree = layout, seq = msg.seq or 0}
    elseif method == "evaluate" then
        if not stored_model then
            return {method = "eval_result", ok = false,
                    error = "no model", seq = msg.seq or 0}
        end
        if type(msg.formula) ~= "string" or msg.formula == "" then
            return {method = "eval_result", ok = false,
                    error = "no formula", seq = msg.seq or 0}
        end
        local feature_set = msg_features(msg)
        -- validate the model has no errors (warnings are okay);
        -- coerce first — restore_model runs before the client's features
        -- are known, so a restored model may still hold numeric-looking
        -- string outcomes
        coerce_numeric_outcomes(stored_model, feature_set)
        local problems = validate_model(stored_model, feature_set)
        for _, p in ipairs(problems) do
            if p.sev == "error" then
                return {method = "eval_result", ok = false,
                        error = "model has errors", seq = msg.seq or 0}
            end
        end
        -- parse the formula
        local parse = get_parser()
        local ok, ast = pcall(parse, msg.formula, feature_set)
        if not ok then
            local from, to_pos, expected, msg_error
            if type(ast) == "table" then
                if ast.positional then
                    from = ast.positional.from
                    to_pos = ast.positional.to
                end
                -- same convention as check_formula: only complete the
                -- formula when the failure sits at end-of-input
                if not (from and from <= #msg.formula) then
                    expected = resolve_suggests(stored_model, msg.formula,
                                                from, ast,
                                                feature_set)
                end
                if ast.key == "parsing_error" then
                    msg_error = nil
                else
                    msg_error = ast.key or tostring(ast)
                end
            else
                msg_error = tostring(ast)
            end
            return {method = "eval_result", ok = false,
                    error = msg_error, from = from, ["to"] = to_pos,
                    expected = expected, seq = msg.seq or 0}
        end
        -- load the BN builder, model checker, and options manager
        local make_bn, bn_err = require_module("bayesian_network.bayesian_network")
        if not make_bn then
            return {method = "eval_result", ok = false,
                    error = "BN builder not available: " .. tostring(bn_err),
                    seq = msg.seq or 0}
        end
        local model_checker, mc_err = require_module("model_checker.model_checker")
        if not model_checker then
            return {method = "eval_result", ok = false,
                    error = "model checker not available: " .. tostring(mc_err),
                    seq = msg.seq or 0}
        end
        local options_manager, om_err = require_module("lib.options_manager")
        if not options_manager then
            return {method = "eval_result", ok = false,
                    error = "options manager not available: " .. tostring(om_err),
                    seq = msg.seq or 0}
        end
        local bn = get_cached_bn()
        if not bn then
            local ok2, bn2 = pcall(model_to_bn, stored_model, make_bn)
            if not ok2 then
                return {method = "eval_result", ok = false,
                        error = "could not build Bayesian network: " .. tostring(bn2),
                        seq = msg.seq or 0}
            end
            bn = bn2
            cached_bn = bn
            cached_for_model = stored_model
        end
        local info = collect_bn_info(bn, feature_set)
        local serr = validate_property(ast, "any", info)
        if serr then
            return eval_semantic_error(serr, msg.seq)
        end
        -- outcomes: a Boolean formula (whole or focused subformula) asks
        -- for its outcome distribution ("the possible outcomes") rather
        -- than the claim text — the probability the formula holds,
        -- rendered as {true = p, false = 1-p} like a permanent node's
        -- marginal.  Query heads are exempt: MAP/MPE's assignment and
        -- IDP/INFL's constant are the useful answers, not a truth
        -- probability; non-Boolean roots (P(...), bare variables,
        -- arithmetic) fail the "boolean" check and are not wrapped.
        local eval_ast = ast
        local opname = (ast:get_type() == "operator")
                       and ast:get_operator_name() or nil
        local query_head = opname == "map" or opname == "mpe"
                        or opname == "idp" or opname == "infl"
        if msg.outcomes and not query_head
           and validate_property(ast, "boolean", info) == nil then
            local okp, past = pcall(parse, "P(" .. msg.formula .. ")",
                                    feature_set)
            if okp and type(past) == "table" and past.get_type then
                eval_ast = past
            end
        end
        local ex = get_explainer()
        local ann = ex and ex.explain_segments(ast, info) or nil
        local explanation = ann and ann.text or nil
        local segments = ann and ann.segments or nil
        collectgarbage("stop")
        ok, res = pcall(function()
            local opts = options_manager.make_options_init({
                num_samples = msg.num_samples or "1E6",
                solvers = msg.solvers,
                enable_solvers = msg.enable_solvers,
                disable_solvers = msg.disable_solvers,
                features = msg.features,
            })
            return model_checker(bn, eval_ast, opts)
        end)
        collectgarbage("restart")
        if not ok then
            local err = res
            if type(res) == "table" then
                err = res.key or tostring(res)
            end
            return {method = "eval_result", ok = false,
                    error = tostring(err), seq = msg.seq or 0}
        end
        if eval_ast ~= ast and type(res) == "number" then
            res = setmetatable({["true"] = res, ["false"] = 1 - res},
                               {__order = {"false", "true"}})
        end
        return {method = "eval_result", ok = true,
                result = format_result(res),
                distribution = dist_payload(res),
                explanation = explanation,
                explanation_segments = segments,
                seq = msg.seq or 0}
    elseif method == "resolve_node_formula" then
        -- "nodeformula": resolve a node's defining BayesL formula into
        -- concrete CPT rows (see the NF_* helpers above)
        local feature_set = msg_features(msg)
        local function refuse(err, extra)
            local r = {method = "nformula_result", ok = false,
                       node = msg.node, error = err,
                       seq = msg.seq or 0}
            if extra then
                for k, v in pairs(extra) do r[k] = v end
            end
            return r
        end
        local function refuse_semantic(serr)
            local from, to_pos = pos_to_table(serr.positional)
            return refuse(serr.msg or serr.key,
                          {from = from, ["to"] = to_pos})
        end
        if not (feature_set and feature_set.nodeformula) then
            return refuse("nodeformula feature is not enabled")
        end
        if not stored_model then
            return refuse("no model")
        end
        if type(msg.formula) ~= "string"
           or msg.formula:match("^%s*$") then
            return refuse("no formula")
        end
        local target, byId = nil, {}
        for _, nd in ipairs(stored_model.nodes or {}) do
            byId[nd.id] = nd
            if nd.id == msg.node then target = nd end
        end
        if not target then return refuse("unknown node") end
        -- the node's parents in edge order define the CPT rows
        local parents = {}
        for _, e in ipairs(stored_model.edges or {}) do
            if e.to == msg.node then parents[#parents + 1] = e.from end
        end
        local pnodes = {}
        for i, pid in ipairs(parents) do
            local pn = byId[pid]
            if not pn then return refuse("unknown parent") end
            pnodes[i] = pn
        end
        -- resolve needs an evaluable model (same gate as evaluate)
        coerce_numeric_outcomes(stored_model, feature_set)
        for _, p in ipairs(validate_model(stored_model, feature_set)) do
            if p.sev == "error" then
                return refuse("model has errors")
            end
        end
        -- parse the formula under the request's features
        local parse = get_parser()
        local ok, ast = pcall(parse, msg.formula, feature_set)
        if not ok then
            local from, to_pos, expected, msg_error
            if type(ast) == "table" then
                if ast.positional then
                    from = ast.positional.from
                    to_pos = ast.positional.to
                end
                -- only complete at end-of-input (check_formula's rule)
                if not (from and from <= #msg.formula) then
                    expected = resolve_suggests(stored_model, msg.formula,
                                                from, ast,
                                                feature_set)
                end
                if ast.key ~= "parsing_error" then
                    msg_error = ast.key or tostring(ast)
                end
            else
                msg_error = tostring(ast)
            end
            return refuse(msg_error, {from = from, ["to"] = to_pos,
                                      expected = expected})
        end
        local make_bn, bn_err = require_module("bayesian_network.bayesian_network")
        if not make_bn then
            return refuse("BN builder not available: " .. tostring(bn_err))
        end
        local model_checker, mc_err = require_module("model_checker.model_checker")
        if not model_checker then
            return refuse("model checker not available: " .. tostring(mc_err))
        end
        local options_manager, om_err = require_module("lib.options_manager")
        if not options_manager then
            return refuse("options manager not available: " .. tostring(om_err))
        end
        local bn_ok, bn = pcall(model_to_bn, stored_model, make_bn)
        if not bn_ok then
            return refuse("could not build Bayesian network: "
                          .. tostring(bn))
        end
        local info = collect_bn_info(bn, feature_set)
        -- variable restriction: every model-variable identifier must be
        -- a declared parent of the node
        local parent_set = {}
        for _, pn in ipairs(pnodes) do parent_set[pn.name] = true end
        local verr = nf_walk_vars(ast, info, parent_set, {},
                                  tostring(target.name))
        if verr then return refuse_semantic(verr) end
        -- kind: variable term or Boolean claim
        local kind
        if varterm.is_variable_term(ast) then
            kind = "term"
        elseif ast:get_type() == "operator"
           and (NF_BOOL_OPS[ast:get_operator_name()]
                or NF_CMP_OPS[ast:get_operator_name()]) then
            kind = "claim"
        else
            return refuse_semantic(
                make_semantic_error("node_formula_kind",
                                    ast:get_positional()))
        end
        -- deep validation: the term/claim must still satisfy the usual
        -- semantic rules (outcome membership, domain merges, ...)
        local serr
        if kind == "term" then
            if ast:get_type() == "identifier" then
                serr = validate_property(ast, "any", info)
            elseif is_numexpr_node(ast) then
                serr = validate_numexpr(ast, info)
            else
                serr = validate_varterm(ast, info)
            end
        else
            serr = validate_property(ast, "boolean", info)
        end
        if serr then return refuse_semantic(serr) end
        -- evaluate as P(formula): a varterm yields its marginal table,
        -- a claim its probability of holding.  "marginal" is forced —
        -- it is an evaluation detail here, not a user-facing opt-in.
        local fset_eval = {}
        for k in pairs(feature_set) do fset_eval[k] = true end
        fset_eval.marginal = true
        local okp, past = pcall(parse, "P(" .. msg.formula .. ")",
                                fset_eval)
        if not okp or type(past) ~= "table" then
            return refuse("could not prepare the formula for evaluation")
        end
        local opts = options_manager.make_options_init({
            num_samples = msg.num_samples or "1E6",
            features = fset_eval,
        })
        local pnames, pouts = {}, {}
        for i, pn in ipairs(pnodes) do
            pnames[i] = pn.name
            pouts[i] = pn.outcomes
        end
        -- rows enumerate the parent configurations in edge order, the
        -- last parent varying fastest (model_to_table's convention)
        local np = #pnodes
        local strides, stride = {}, 1
        for p = np, 1, -1 do
            strides[p] = stride
            stride = stride * math.max(1, #pouts[p])
        end
        local domain, rows_out = nil, {}
        for r = 0, stride - 1 do
            -- fix each parent at this row's values: a point-mass CPT
            -- makes the row's assignment certain evidence — equivalent
            -- to conditioning, but without zero-probability evidence or
            -- outcome-name quoting problems
            local saved = {}
            for p = 1, np do
                local var = bn.variables[pnames[p]]
                saved[p] = var.probabilities
                var.probabilities = nil
                local v = pouts[p][math.floor(r / strides[p])
                                   % #pouts[p] + 1]
                bn:set_probabilies(pnames[p], {}, {[v] = 1})
            end
            local okr, res = pcall(model_checker, bn, past, opts)
            for p = 1, np do
                bn.variables[pnames[p]].probabilities = saved[p]
            end
            if not okr then
                local key = type(res) == "table" and res.key
                            or tostring(res)
                local from, to_pos
                if type(res) == "table" then
                    from, to_pos = pos_to_table(res.positional)
                end
                return refuse(tostring(key),
                              {from = from, ["to"] = to_pos})
            end
            local dist
            if type(res) == "number" then
                -- a Boolean claim: P returns P(claim), the domain is
                -- the solver's truth domain
                domain = domain or {"F", "T"}
                dist = {F = 1 - res, T = res}
            else
                if not domain then
                    local mt = getmetatable(res)
                    domain = mt and mt.__order
                    if not domain then
                        domain = {}
                        for k in pairs(res) do
                            domain[#domain + 1] = k
                        end
                        table.sort(domain, function(a, b)
                            return tostring(a) < tostring(b)
                        end)
                    end
                end
                dist = res
            end
            local row = {}
            for c = 1, #domain do
                row[c] = dist[domain[c]] or 0
            end
            rows_out[r + 1] = row
        end
        return {method = "nformula_result", ok = true, node = msg.node,
                domain = domain or {}, rows = rows_out,
                seq = msg.seq or 0}
    end
    error("unknown method: " .. tostring(method))
end

return function(raw, hooks)
    local ok, msg = pcall(json.decode, raw)
    local res
    if not ok or type(msg) ~= "table" then
        res = {method = "error", reason = "invalid json"}
    else
        ok, res = pcall(handle, msg, hooks)
        if not ok then
            res = {method = "error", reason = tostring(res)}
        end
    end
    return json.encode(res)
end
