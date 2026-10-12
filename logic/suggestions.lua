---
--- Suggestion resolver: turns the parse error's annotation channel
--- (expectation labels, suggestion payloads, and the match journal of
--- operand-end / separator notes) into the concrete, ordered token
--- list the client offers.
---
--- The labels a parse registers at its farthest position drive the
--- emission order and the fixed token vocabulary (EXPECTED_TOKENS);
--- the journal answers the "which operand/slot is here" questions the
--- old position classifier reconstructed by re-scanning the input:
--- operand ends carry their AST node and the scope they were parsed in
--- (slot/role/owner), separators carry the slot that follows them.
---
--- env supplies everything model- or request-derived:
---   env.formula        the full formula text
---   env.pos            the byte position the suggestions are for
---   env.features       the active feature set
---   env.model          the model ({nodes={name,outcomes}})
---   env.bound          LET-bound names visible at pos, ordered
---   env.bound_kind(n)  -> "boolq"|"number"|nil for bound names
---   env.let_scope      let_scope_at(formula, pos) or nil
---   env.let_scope_at   fn(p) -> let scope at another position
---   env.varterm_domain(src) -> static domain of a varterm AST or
---                            source text, or nil
---   env.partial        identifier token ending before pos (or nil)
---   env.tok_start      its start position
---

local operators = require "logic.operators"
local dist_family = require "logic.dist_family"
local varterm = require "logic.varterm"
local util = require "lib.util"

local suggestions = {}

-- --------------------------------------------------------------------
-- the fixed vocabulary (canonical spellings) per expectation label
-- --------------------------------------------------------------------

local EXPECTED_TOKENS = {
    expected_phi            = {"¬", "ℙ(", "MAP(", "MPE(", "IDP(",
                               "INFL(", "(", "□", "<identifier>"},
    expected_psi            = {"ℙ(", "(", "□", "<number>"},
    expected_value          = {"ℙ(", "(", "□", "<number>"},
    expected_identifier     = {"<identifier>", "□"},
    expected_numexpr        = {"<identifier>", "(", "□", "<number>"},
    expected_number         = {"<number>"},
    expected_probability    = {"□", "<number>"},
    expected_pdist_arg      = {"□", "<identifier>", "<number>"},
    expected_compare        = {"=", "≤", "≥", "<", ">"},
    expected_logical_operator = {"∧", "∨", "↑", "↓", "→", "↔", "⊕"},
    expected_arithmetic_operator = {"×", "−", "+", "÷"},
    expected_lparen         = {"("},
    expected_rparen         = {")"},
    expected_bar            = {"|"},
    expected_comma          = {","},
    expected_colon          = {":"},
    expected_maps_to        = {"↦"},
    expected_let_name       = {"<name>"},
    expected_assign         = {"="},
    expected_let_tail       = {";", "IN"},
    expected_lbrack         = {"["},
    expected_rbrack         = {"]"},
    expected_rbrack_or_bar  = {"]", "|"},
    expected_eof            = {"<end of input>"},
}
suggestions.EXPECTED_TOKENS = EXPECTED_TOKENS

-- feature + fancy + ASCII keyword spelling per moment operator, in
-- display order — used by every keyword-emission site
local MOMENT_STARTERS = {
    {"expect", "𝔼(", "E("},
    {"variance", "𝕍(", "VAR("},
    {"sd", "σ(", "SD("},
}
local MOMENT_OPS = {expect = true, variance = true, sd = true}

-- keywords opening a Boolean operand; the P(/ℙ( forms double as psi
local PHI_KEYWORDS = {"P(", "MAP(", "MPE(", "IDP(", "INFL("}
local BOOLQ_KEYWORDS = {MAP = true, MPE = true, IDP = true, INFL = true}
local VARTERM_KEYWORDS = {DIST = true, RENAME = true, MUX = true}

local LOGICAL_OP_NAMES = {["not"] = true, ["and"] = true,
                          ["nand"] = true, ["or"] = true,
                          ["nor"] = true, ["implication"] = true,
                          ["biimplication"] = true, ["xor"] = true}
local COMPARE_OP_NAMES = {less = true, less_or_equal = true,
                          equal = true, greater_or_equal = true,
                          greater = true}
local ARITH_OP_NAMES = {plus = true, minus = true, times = true,
                        divide = true}
local VARTERM_OPS = {dist = true, rename = true, mux = true}
local BOOLQ_OPS = {map = true, mpe = true, idp = true, infl = true}
local function is_pdist_op(op)
    return dist_family.keywords[op] ~= nil
        or (op and dist_family.keywords[op:upper()])
end

local function is_placeholder(t)
    return type(t) == "string"
       and t:sub(1, 1) == "<" and t:sub(-1, -1) == ">"
end

-- candidate spellings for a fresh LET binding name, in offer order —
-- single lowercase letters cannot shadow the (capitalised) model
-- variables and read differently from bound names like "X"/"H"
local LET_NAME_POOL = {"x", "y", "z", "a", "b", "c", "k", "p", "q",
                       "r", "s", "t", "u", "v", "w"}

local function let_fresh_name(env)
    local taken = {let = true, ["in"] = true,
                   ["true"] = true, ["false"] = true}
    for _, n in ipairs(env.bound or {}) do
        taken[n:lower()] = true
    end
    local function free(n)
        return not taken[n:lower()]
           and not (env.is_var and env.is_var(n))
    end
    for _, n in ipairs(LET_NAME_POOL) do
        if free(n) then return n end
    end
    local i = 1
    while true do
        local n = "x" .. i
        if free(n) then return n end
        i = i + 1
    end
end

-- the tappable fresh-name token for the LET name slot: padded with a
-- space only on the side that faces a word char — a bare splice would
-- fuse with the keyword on the left ("LETx") or a word char on the
-- right ("xIN"), while a space where none is needed shows as a stray
-- gap after insertion ("LET x ").  The <name> marker alongside it is
-- the UI's signal to offer the letter keyboard.
local function let_name_token(formula, pos, nm)
    local before = pos > 1 and formula:sub(pos - 1, pos - 1) or ""
    local after = pos <= #formula and formula:sub(pos, pos) or ""
    local lead = before ~= "" and before:match("[%s%(%[]") == nil
                 and " " or ""
    local trail = after:match("[%a%d_]") ~= nil and " " or ""
    return lead .. nm .. trail
end

-- the arithmetic-infix tokens: all four are builtin (the former
-- "arith" feature gate only ever held + and ÷)
local function arith_tokens(feature_set)
    return EXPECTED_TOKENS["expected_arithmetic_operator"]
end

local function add_pdist_keywords(list)
    for _, kw in ipairs(dist_family.order) do
        list[#list + 1] = kw .. "("
    end
end

-- --------------------------------------------------------------------
-- model accessors
-- --------------------------------------------------------------------

local function get_model_names(model)
    local names = {}
    for _, n in ipairs(model and model.nodes or {}) do
        if type(n) == "table" and type(n.name) == "string"
           and n.name ~= "" then
            names[#names + 1] = n.name
        end
    end
    return names
end

local function get_model_outcomes(model)
    local seen = {}
    local out = {}
    for _, n in ipairs(model and model.nodes or {}) do
        if type(n) == "table" and type(n.outcomes) == "table" then
            for _, v in ipairs(n.outcomes) do
                local sv = tostring(v)
                if not seen[sv] then
                    seen[sv] = true
                    out[#out + 1] = sv
                end
            end
        end
    end
    return out
end

local function get_model_node_info(model, name)
    for _, n in ipairs(model and model.nodes or {}) do
        if type(n) == "table" and n.name == name
           and type(n.outcomes) == "table" then
            local set = {}
            for _, v in ipairs(n.outcomes) do
                set[tostring(v)] = true
            end
            return {name = n.name, outcomes = n.outcomes, set = set}
        end
    end
    return nil
end

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

local function numeric_name(model, name)
    local info = name and get_model_node_info(model, name) or nil
    return info ~= nil and node_is_numeric(info)
end

local function numeric_var_names(model)
    local out = {}
    for _, n in ipairs(model and model.nodes or {}) do
        if type(n) == "table" and type(n.name) == "string"
           and node_is_numeric(n) then
            out[#out + 1] = n.name
        end
    end
    return out
end

-- variables sharing at least one outcome with `left_name` (numeric
-- variables are mutually comparable)
local function comparable_names(model, left_name, left_info)
    local out = {}
    local numeric = node_is_numeric(left_info)
    for _, n in ipairs(model and model.nodes or {}) do
        if type(n) == "table" and n.name ~= left_name
           and type(n.outcomes) == "table" then
            if numeric then
                if node_is_numeric(n) then
                    out[#out + 1] = n.name
                end
            else
                for _, v in ipairs(n.outcomes) do
                    if left_info.set[tostring(v)] then
                        out[#out + 1] = n.name
                        break
                    end
                end
            end
        end
    end
    return out
end

-- --------------------------------------------------------------------
-- small lexical helpers (unchanged from the text era — they inspect
-- single tokens, not structure)
-- --------------------------------------------------------------------

local function is_space_byte(b)
    return b == 32 or b == 9 or b == 10 or b == 13
end

local function is_id_byte(b)
    return (b >= 65 and b <= 90) or (b >= 97 and b <= 122)
        or (b >= 48 and b <= 57) or b == 95
end

-- the identifier token ending just before `pos` (never a pure digit
-- run) plus its start
local function last_identifier_before(formula, pos)
    if not formula or not pos or pos <= 1 then return nil end
    local p = pos - 1
    while p >= 1 and is_space_byte(formula:byte(p)) do p = p - 1 end
    if p < 1 or not is_id_byte(formula:byte(p)) then return nil end
    local end_pos = p
    while p >= 1 and is_id_byte(formula:byte(p)) do p = p - 1 end
    local start_pos = p + 1
    if formula:sub(start_pos, start_pos):match("%d") then
        return nil
    end
    return formula:sub(start_pos, end_pos), start_pos
end

-- --------------------------------------------------------------------
-- the journal: operand ends and separators the parse walked, in match
-- order.  Replaces the old position classifier's backward text scans.
-- --------------------------------------------------------------------

local function make_journal(formula, notes)
    local J = {formula = formula, notes = notes or {}}

    local function gap_space(a, b)
        -- the text between note-end a and position b is all whitespace
        return a >= b or formula:sub(a, b - 1):match("^%s*$") ~= nil
    end
    J.gap_space = gap_space

    -- the operand ending right before p (only whitespace between)
    local memo_oe = {}
    function J.oend_before(p)
        local e = memo_oe[p]
        if e == nil then
            local best
            for _, n in ipairs(J.notes) do
                if n.kind == "oend" and n.to and n.to <= p
                   and gap_space(n.to, p) then
                    if not best or n.to > best.to
                       or (n.to == best.to and n.from > best.from) then
                        best = n
                    end
                end
            end
            e = best or false
            memo_oe[p] = e
        end
        return e or nil
    end

    -- an operand starting exactly at p
    local memo_os = {}
    function J.oend_at(p)
        local e = memo_os[p]
        if e == nil then
            local best
            for _, n in ipairs(J.notes) do
                if n.kind == "oend" and n.from == p then
                    if not best or n.to > best.to then best = n end
                end
            end
            e = best or false
            memo_os[p] = e
        end
        return e or nil
    end

    -- the separator (sep/csep/pbar/psep) ending right before p
    local memo_sep = {}
    function J.sep_before(p)
        local e = memo_sep[p]
        if e == nil then
            local best
            for _, n in ipairs(J.notes) do
                if n.kind ~= "oend" and n.to and n.to <= p
                   and gap_space(n.to, p) then
                    if not best or n.to > best.to then best = n end
                end
            end
            e = best or false
            memo_sep[p] = e
        end
        return e or nil
    end

    -- the operand (atom chain over arithmetic operators) ending right
    -- before p: start, last-atom kind, its keyword, arith flag, node
    local memo_ot = {}
    function J.operand_tail(p)
        local e = memo_ot[p]
        if e ~= nil then
            if e == false then return nil end
            return e[1], e[2], e[3], e[4], e[5]
        end
        local o = J.oend_before(p)
        if not o then
            memo_ot[p] = false
            return nil
        end
        local start = o.from
        local kind, kw, node = o.okind, o.kw, o.node
        local has_arith = false
        while true do
            local s = J.sep_before(start)
            if s and s.kind == "csep" and s.cls == "arith" then
                has_arith = true
                local o2 = J.oend_before(s.from)
                if not o2 then break end
                start = o2.from
            else
                break
            end
        end
        e = {start, kind, kw, has_arith, node}
        memo_ot[p] = e
        return start, kind, kw, has_arith, node
    end

    -- the comparison/map-arrow operator ending right before p, plus the
    -- trailing identifier run on its left (nil when the left side ends
    -- in ')' or ']') and the operator's own position
    local memo_ct = {}
    function J.compare_tail(p)
        local e = memo_ct[p]
        if e ~= nil then
            if e == false then return nil end
            return e[1], e[2], e[3]
        end
        local sep
        for _, n in ipairs(J.notes) do
            if n.kind == "csep" and n.cls == "cmp" and n.to
               and n.to <= p and gap_space(n.to, p) then
                if not sep or n.to > sep.to then sep = n end
            end
        end
        if not sep then
            memo_ct[p] = false
            return nil
        end
        local op_pos = sep.from
        local q = sep.from - 1
        while q >= 1 and is_space_byte(formula:byte(q)) do q = q - 1 end
        if q < 1 or not is_id_byte(formula:byte(q)) then
            e = {nil, nil, op_pos}
            memo_ct[p] = e
            return nil, nil, op_pos
        end
        local end_pos = q
        while q >= 1 and is_id_byte(formula:byte(q)) do q = q - 1 end
        local start_pos = q + 1
        -- a digit run after '.' is a number's fraction, not a name
        if formula:sub(q, q) == "."
           and formula:sub(start_pos, end_pos):match("^%d+$") then
            e = {nil, nil, op_pos}
            memo_ct[p] = e
            return nil, nil, op_pos
        end
        e = {formula:sub(start_pos, end_pos), start_pos, op_pos}
        memo_ct[p] = e
        return e[1], e[2], e[3]
    end

    -- the slot an operand starting at p occupies: an operand that
    -- already ENDED at p means p trails it ("other"); an operand
    -- starting at p takes its own scope's slot; a separator just
    -- before p names the slot that follows it
    function J.slot(p)
        if J.oend_before(p) then return "other" end
        -- the separator right before p names the slot it opens — the
        -- operand's own note only wins when no separator intervenes
        -- (its slot stamp is ambient scope, not the grammar's slot)
        local s = J.sep_before(p)
        if s then
            if s.nslot then return s.nslot end
            if s.kind == "csep" or s.kind == "mapsep" then
                -- comparison and map arrows open a compare-class slot
                return s.cls == "arith" and "arith" or "compare"
            end
            return "bool"   -- sep/psep/pbar
        end
        local o = J.oend_at(p)
        if o then return o.slot or "any" end
        return nil
    end

    return J
end

-- --------------------------------------------------------------------
-- semantic classification of the trailing operand's AST node
-- --------------------------------------------------------------------

-- "name" (variable/outcome literal), "number", "prob" (P/moment),
-- "boolq" (MAP/MPE/IDP/INFL), "varterm" (DIST/RENAME/MUX/FAMILY),
-- "modify", "claim", "numexpr", "box", "group"
local function node_cat(node, env)
    if type(node) ~= "table" or type(node.get_type) ~= "function" then
        return nil
    end
    local t = node:get_type()
    if t == "identifier" then
        local nm = node:get_identifier()
        local bk = env.bound_kind and env.bound_kind(nm)
        if bk then return bk end
        return "name"
    end
    if t == "value" or t == "number" then return "number" end
    if t == "box" then return "box" end
    if t ~= "operator" then return "name" end
    local op = node:get_operator_name()
    if op == "let" or op == "binding" then
        return node_cat(node:get_child(node:get_num_children()), env)
    end
    if op == "modify_probability" then return "modify" end
    if COMPARE_OP_NAMES[op] or LOGICAL_OP_NAMES[op] then
        return "claim"
    end
    if BOOLQ_OPS[op] then return "boolq" end
    if op == "prob" or MOMENT_OPS[op] then return "prob" end
    if op == "conditional" then
        local left = node:get_child(1)
        while left and left:get_type() == "operator"
              and left:get_operator_name() == "conditional" do
            left = left:get_child(1)
        end
        if left and left:get_type() == "identifier" then
            return "varterm"
        end
        return "claim"
    end
    if VARTERM_OPS[op] or is_pdist_op(op) then return "varterm" end
    if ARITH_OP_NAMES[op] then
        if env.features and env.features.numvar
           and varterm.is_numexpr(node) then
            return "numexpr"
        end
        return "number"
    end
    return "term"
end

-- can the operand still yield a Boolean claim (svc's bool-walk
-- completability, structural over the AST)
local function bool_completable(node, env)
    local cat = node_cat(node, env)
    if cat == nil then return false end
    if cat == "box" then return true end
    if cat == "boolq" or cat == "claim" then
        if type(node) == "table" and node.get_operator_name
           and LOGICAL_OP_NAMES[node:get_operator_name()] then
            for i = 1, node:get_num_children() do
                if not bool_completable(node:get_child(i), env) then
                    return false
                end
            end
        end
        return true
    end
    if cat == "name" then
        local nm = node:get_identifier()
        if env.bound_kind and env.bound_kind(nm) == "boolq" then
            return true
        end
        if env.features and env.features.marginal
           and (get_model_node_info(env.model, nm) ~= nil
                or (env.bound_kind and env.bound_kind(nm) ~= nil)) then
            return true
        end
        return false
    end
    if cat == "varterm" or cat == "numexpr" then
        return env.features ~= nil and env.features.marginal ~= nil
    end
    return false
end

local function numeric_completable(node, env)
    local cat = node_cat(node, env)
    if cat == "box" then return true end
    if cat == "number" or cat == "prob" or cat == "numexpr" then
        return true
    end
    if cat == "name" then
        local nm = node:get_identifier()
        if env.features and env.features.numvar
           and (env.numeric and env.numeric(nm)
                or (env.bound_kind
                    and env.bound_kind(nm) == "number")) then
            return true
        end
        return false
    end
    if cat == "varterm" then
        if not (env.features and env.features.numvar) then
            return false
        end
        local dom = env.varterm_domain and env.varterm_domain(node)
        if type(dom) ~= "table" then return false end
        for _, v in ipairs(dom) do
            if type(v) ~= "number" then return false end
        end
        return #dom > 0
    end
    if cat == "modify" then
        local inner = node.get_child_or_nil and node:get_child_or_nil(1)
        return inner ~= nil and numeric_completable(inner, env)
    end
    return false
end

local function term_completable(node, env)
    local cat = node_cat(node, env)
    return cat ~= nil and cat ~= "claim" and cat ~= "boolq"
end

local function termish_completable(node, env)
    local cat = node_cat(node, env)
    if cat == nil then return false end
    return cat ~= "number" and cat ~= "prob" and cat ~= "modify"
end

-- does the arithmetic subtree contain only variable/number/box leaves
-- (no call nodes) — svc's `not text:find("[%a_]%s*%(")` check
local numexpr_leaf
numexpr_leaf = function(node)
    if type(node) ~= "table" or type(node.get_type) ~= "function" then
        return false
    end
    local t = node:get_type()
    if t == "identifier" or t == "value" or t == "number"
       or t == "box" then
        return true
    end
    if t ~= "operator" then return false end
    local op = node:get_operator_name()
    if not ARITH_OP_NAMES[op] then return false end
    for i = 1, node:get_num_children() do
        if not numexpr_leaf(node:get_child(i)) then return false end
    end
    return true
end

-- --------------------------------------------------------------------
-- the candidates valid for an identifier slot — role-resolved via the
-- journal + payload env stamps instead of text scans
-- --------------------------------------------------------------------

local function identifier_candidates(env, J, pc0, want_compare_tail, cand_pos)
    local model, feature_set = env.model, env.features
    local pos = env.pos

    local function compare_candidates(left_name)
        if left_name and left_name:match("^%d") then
            if feature_set and feature_set.numval then
                return numeric_var_names(model)
            end
            return {}
        end
        local left_info = left_name
            and get_model_node_info(model, left_name) or nil
        if left_info then
            if node_is_numeric(left_info)
               and not (feature_set and feature_set.numval) then
                return {}
            end
            local items = {}
            for _, v in ipairs(left_info.outcomes) do
                items[#items + 1] = tostring(v)
            end
            for _, n in ipairs(comparable_names(model, left_name,
                                                left_info)) do
                items[#items + 1] = n
            end
            return items
        end
        -- an outcome literal on the left: the owners declaring it
        local owners = {}
        for _, n in ipairs(model and model.nodes or {}) do
            if type(n) == "table" and type(n.outcomes) == "table" then
                for _, v in ipairs(n.outcomes) do
                    if tostring(v) == left_name then
                        owners[#owners + 1] = n.name
                        break
                    end
                end
            end
        end
        if #owners > 0 then return owners end
        return get_model_outcomes(model)
    end

    local function names_then_values()
        local items = get_model_names(model)
        local seen = {}
        for _, it in ipairs(items) do seen[it] = true end
        for _, n in ipairs(model and model.nodes or {}) do
            if type(n) == "table" and type(n.outcomes) == "table"
               and ((feature_set and feature_set.numval)
                    or not node_is_numeric(n)) then
                for _, v in ipairs(n.outcomes) do
                    local sv = tostring(v)
                    if not seen[sv] then
                        seen[sv] = true
                        items[#items + 1] = sv
                    end
                end
            end
        end
        return items
    end

    -- intervention bracket: the role stamp tells which slot
    local brole = pc0.brole
    if brole then
        if brole == "target" or brole == "condvar" then
            return {items = get_model_names(model)}
        end
        if brole == "mapkey" or brole == "mapval" then
            local ti = pc0.btarget
                and get_model_node_info(model, pc0.btarget) or nil
            local items = {}
            for _, v in ipairs(ti and ti.outcomes or {}) do
                items[#items + 1] = tostring(v)
            end
            return {items = items}
        end
        -- condval: outcome of the condition's left variable or a
        -- comparable variable
        return {items = compare_candidates(J.compare_tail(cand_pos or pos))}
    end

    -- DIST/RENAME/MUX/FAMILY interiors: the role decides
    local vc_owner = pc0.owner
    if vc_owner == "DIST" or vc_owner == "RENAME" or vc_owner == "MUX"
       or dist_family.keywords[vc_owner] then
        local vc_role = pc0.role
        if vc_role == "pdist_arg" then
            if vc_owner == "DEGENERATE" then
                return {items = get_model_outcomes(model)}
            end
            return {items = {}}
        end
        if vc_owner == "MUX" then
            if vc_role == "first" or vc_role == "selval"
               or vc_role == "mixkey" then
                return {items = names_then_values()}
            end
            if vc_role == "selkey" then
                local dom = pc0.source and env.varterm_domain
                    and env.varterm_domain(pc0.source)
                if dom then
                    local items = {}
                    for _, v in ipairs(dom) do
                        items[#items + 1] = tostring(v)
                    end
                    return {items = items}
                end
                return {items = get_model_outcomes(model)}
            end
            return {items = {}}   -- mixprob: numbers only
        end
        if vc_owner == "RENAME" and vc_role == "source" then
            return {items = get_model_names(model)}
        end
        if vc_owner == "RENAME" and vc_role == "key" then
            local dom = pc0.source and env.varterm_domain
                and env.varterm_domain(pc0.source)
            if dom then
                local items = {}
                for _, v in ipairs(dom) do
                    items[#items + 1] = tostring(v)
                end
                return {items = items}
            end
            return {items = get_model_outcomes(model)}
        end
        return {items = get_model_outcomes(model)}
    end

    if want_compare_tail then
        local left_name, _, op_pos = J.compare_tail(cand_pos or pos)
        if not left_name and op_pos then
            -- left side ends in ')' or ']': a varterm literal's right
            -- side takes that term's outcome names
            local ls = J.operand_tail(op_pos)
            local lnode = ls and select(5, J.operand_tail(op_pos))
            local dom = lnode and env.varterm_domain
                and env.varterm_domain(lnode)
            if dom then
                local items = {}
                for _, v in ipairs(dom) do
                    items[#items + 1] = tostring(v)
                end
                return {items = items}
            end
        end
        if left_name then
            -- arithmetic in the left operand makes the right side a
            -- numeric slot ("X − Y >" takes real-valued variables only)
            local _, _, _, larith, lnode = J.operand_tail(op_pos)
            if larith then
                if feature_set and feature_set.numvar
                   and lnode and numexpr_leaf(lnode) then
                    return {items = numeric_var_names(model)}
                end
                return {items = {}}
            end
            return {items = compare_candidates(left_name)}
        end
    end

    local owner = pc0.owner
    if owner == "IDP" or owner == "INFL"
       or (owner == "MAP" and not pc0.post_bar) then
        return {items = get_model_names(model)}
    end
    if owner == "MOMENT" then
        -- E/VAR/SD reject a string-valued operand up front — only
        -- real-valued variables are candidates
        return {items = numeric_var_names(model)}
    end
    return {items = names_then_values()}
end

-- --------------------------------------------------------------------
-- the resolver: faithful port of the old expand_expected, with the
-- position classifier replaced by the journal + env-stamped payloads
-- --------------------------------------------------------------------

-- err = {expected=…, suggest=…, order=…, notes=…} — the parse
-- result's annotation channel (or a bare label list)
function suggestions.resolve(err, env)
    local labels = err.expected or err.labels or err
    if type(labels) == "string" then labels = {labels} end
    if type(labels) ~= "table" or #labels == 0 then
        return nil
    end
    local label_set = {}
    for _, l in ipairs(labels) do
        label_set[l] = true
    end
    local model, feature_set = env.model, env.features
    local formula, pos = env.formula, env.pos
    local payloads = err.payloads or err.suggest or {}
    local notes = err.notes or {}
    local J = make_journal(formula, notes)

    -- the ambient scope at pos is the stamp of the DEEPEST payload —
    -- continuation payloads registered at the same position but outside
    -- the innermost construct must not override its role
    local pc0 = {}
    local best_depth = -1
    for _, p in ipairs(payloads) do
        local d = p.depth or 0
        if d > best_depth then
            best_depth = d
            for _, k in ipairs({"slot", "role", "owner", "in_cond",
                                "brole", "btarget", "src", "post_bar",
                                "depth"}) do
                pc0[k] = p[k]
            end
        end
        if p.kind == "outcome-of" and pc0.outcome_of == nil then
            pc0.outcome_of = p.var
        end
    end
    pc0.source = pc0.src
    local partial, tok_start = env.partial, env.tok_start
    if partial == nil then
        partial, tok_start = last_identifier_before(formula, pos)
        if partial == "" then partial, tok_start = nil, nil end
    end
    -- a completed operand's own end note refines the context: when the
    -- operand is the token under the cursor (a partial token's own
    -- note, or a complete operand with no separator between its end
    -- and the offer position) its stamps win over the continuation
    -- payloads, which describe the NEXT slot; behind a separator only
    -- fields the payloads left blank apply
    local last_o = J.oend_before(pos)
    if partial then
        local own = J.oend_at(tok_start)
        if own then last_o = own end
    end
    if last_o then
        local current
        if partial then
            current = last_o.from == tok_start
        else
            local s = J.sep_before(pos)
            current = not (s and s.from >= last_o.to)
        end
        for _, k in ipairs({"role", "brole", "btarget", "owner",
                            "slot", "in_cond", "post_bar"}) do
            if last_o[k] ~= nil and (current or pc0[k] == nil) then
                pc0[k] = last_o[k]
            end
        end
        if pc0.source == nil then pc0.source = last_o.src end
    end
    -- payload-driven context that isn't in the scope stamps: a
    -- "newident" marker means the identifier slot takes fresh names
    -- (no candidate list, partials never dead-end); an "outcome-of"
    -- or "srcof" payload names the governing variable/source
    local free_name_slot = false
    for _, p in ipairs(payloads) do
        if p.cat == "newident" or p.free then free_name_slot = true end
        if p.kind == "srcof" and p.node and pc0.source == nil then
            pc0.source = p.node
        end
        if pc0.source == nil and p.src ~= nil then
            pc0.source = p.src
        end
        if p.kind == "outcome-of" then
            if p.node and pc0.of == nil then pc0.of = p.node end
            if p.var and pc0.outcome_of == nil then
                pc0.outcome_of = p.var
            end
        end
        if p.kind == "pdist-arg" and p.family then
            pc0.owner = p.family
            pc0.role = "pdist_arg"
        end
    end
    -- a scope-stamped source/target node normalises to its identifier
    -- name where the candidate matrices want a name
    local function node_name(v)
        if type(v) == "table" and v.get_identifier then
            local ok, nm = pcall(function() return v:get_identifier() end)
            if ok then return nm end
            return nil
        end
        return v
    end
    pc0.btarget = node_name(pc0.btarget)

    -- `vc` is the varterm-context owner (DIST/RENAME/MUX/named
    -- family) — the old service's `varterm_context`; a "P"/"MAP"/
    -- moment owner is a paren context, not a varterm owner
    local vc_owner = (pc0.owner == "DIST" or pc0.owner == "RENAME"
                      or pc0.owner == "MUX"
                      or (pc0.owner ~= nil
                          and dist_family.keywords[pc0.owner]))
                     and pc0.owner or nil
    local mux_role = vc_owner == "MUX" and pc0.role or nil
    local mux_term = mux_role == "first" or mux_role == "selval"
        or mux_role == "mixkey"
    local ren_source = vc_owner == "RENAME" and pc0.role == "source"
    local term_role = (not vc_owner) or ren_source or mux_term

    -- a separator inside a MUX/DIST/RENAME paren whose text is a map
    -- arrow — the grammar's own "mapsep" notes and the "->"/"→"/"="
    -- separators the term grammar swallowed as implication/comparison
    local function entry_arrow(n)
        local os_ = J.operand_tail(n.from)
        if not os_ then return false end
        local s = J.sep_before(os_)
        if n.sym == "=" then
            return s == nil or s.kind == "comma"
        end
        while s do
            if s.kind == "comma" then return true end
            if s.kind == "mapsep" then return false end
            os_ = J.operand_tail(s.from)
            if not os_ then return false end
            s = J.sep_before(os_)
        end
        return true
    end
    local function is_arrow_note(n)
        if n.owner ~= vc_owner or not n.sym then return false end
        if n.kind == "mapsep" then
            return n.sym == "↦" or entry_arrow(n)
        end
        return (n.kind == "sep" or n.kind == "csep")
            and (n.sym == "->" or n.sym == "→" or n.sym == "=")
            and entry_arrow(n)
    end
    -- inside MUX the FIRST comma decides the form: an entry carrying a
    -- map arrow before it means every entry is "key ↦ weight"
    -- (mixture); a bare selector term means "outcome ↦ branch" rows
    local mux_sel
    local function mux_selector_form()
        if mux_sel ~= nil then return mux_sel end
        mux_sel = false
        local first_comma
        for _, n in ipairs(notes) do
            if n.kind == "comma" and n.owner == "MUX"
               and (not first_comma or n.from < first_comma.from) then
                first_comma = n
            end
        end
        if first_comma then
            mux_sel = true
            for _, s in ipairs(notes) do
                if is_arrow_note(s) and s.to and s.to <= first_comma.from
                then
                    mux_sel = false
                    break
                end
            end
        end
        return mux_sel
    end
    -- inside a DIST/RENAME/MUX paren the term grammar swallows "->"/"="
    -- (and "→") as implication/comparison: a separator carrying that
    -- symbol is the entry's map arrow and the slot after it is the
    -- entry VALUE — never a boolean operand.  For MUX the form decides
    -- branch value ("selval") vs mixture weight ("mixprob").
    -- An arrow symbol is the entry's arrow only when the grammar's own
    -- operator precedence leaves it at the entry's top level: "=" binds
    -- inside the term (a condition's compare — "Grade | I = x" parses
    -- "I = x" inside the condition), so it is an arrow only when the
    -- operand before it opens the entry; "->"/"→" bind the whole term,
    -- so the operand chain before them only has to reach the entry
    -- boundary without crossing another entry's arrow.
    local map_arrow
    do
        local ap = (partial and tok_start or pos) - 1
        while ap >= 1 and is_space_byte(formula:byte(ap)) do
            ap = ap - 1
        end
        for _, n in ipairs(notes) do
            if vc_owner and n.to == ap + 1 and is_arrow_note(n) then
                map_arrow = n
                break
            end
        end
        if map_arrow then
            if vc_owner == "MUX" then
                pc0.role = mux_selector_form() and "selval" or "mixprob"
            else
                pc0.role = "value"
            end
            mux_role = vc_owner == "MUX" and pc0.role or nil
            mux_term = mux_role == "selval"
            ren_source = false
            term_role = mux_term
        end
    end
    -- a MUX key position after the selector comma is constrained to the
    -- selector's domain — the mixture alternative's "mixkey" stamp on
    -- the same operand must not make it a free name
    if vc_owner == "MUX" and not map_arrow then
        -- the operand under the cursor: a partial's own oend starts at
        -- tok_start, a complete operand's ends before pos
        local lo = partial and J.oend_at(tok_start)
                  or J.oend_before(pos)
        if lo and (lo.role == "selkey" or lo.role == "mixkey")
           and mux_selector_form() then
            pc0.role = "selkey"
            mux_role = "selkey"
            mux_term = false
            term_role = false
            if pc0.source == nil then
                for _, n in ipairs(notes) do
                    if n.kind == "oend" and n.role == "selkey" and n.src
                    then
                        pc0.source = n.src
                        break
                    end
                end
            end
        end
    end
    -- a DIST key, a RENAME value and a MUX selector/branch take
    -- free-standing literal names — a partial that prefixes no
    -- candidate is already a complete name there
    if vc_owner == "DIST" and pc0.role == "key"
       or vc_owner == "RENAME" and pc0.role == "value"
       or vc_owner == "MUX" and mux_term then
        free_name_slot = true
    end

    local let_scope = (feature_set and feature_set.let)
                      and env.let_scope or nil
    local function is_bound_name(nm)
        if not (let_scope and nm) then return false end
        for _, b in ipairs(let_scope.names) do
            if b == nm then return true end
        end
        return false
    end
    local function bound_kind(nm)
        return env.bound_kind and env.bound_kind(nm) or nil
    end

    -- kw_call: the partial is a keyword AND a live variable name —
    -- '(' and the name continuations both apply
    local kw_call = false
    if partial and label_set.expected_lparen then
        local function is_keyword()
            for _, kw in ipairs({"P", "MAP", "MPE", "IDP", "INFL"}) do
                if partial == kw then return true end
            end
            if feature_set and feature_set.dist
               and partial == "DIST" then return true end
            if feature_set and feature_set.rename
               and partial == "RENAME" then return true end
            if feature_set and feature_set.mux
               and partial == "MUX" then return true end
            if feature_set and feature_set.dists
               and dist_family.keywords[partial] then return true end
            for _, m in ipairs(MOMENT_STARTERS) do
                if feature_set and feature_set[m[1]]
                   and partial == m[3]:sub(1, -2) then
                    return true
                end
            end
            return false
        end
        if is_keyword() then
            if get_model_node_info(model, partial) ~= nil
               or is_bound_name(partial) then
                kw_call = true
            else
                return {"("}
            end
        end
    end
    local fresh_body = let_scope and let_scope.expect == "body"
        and let_scope.body_at
        and formula:sub(let_scope.body_at, pos - 1):match("^%s*$")
    if fresh_body then
        partial, tok_start = nil, nil
    end
    -- the '=' of a let-binding is an assign, not a comparison
    local let_rhs_operand = false
    if let_scope and let_scope.assign_at then
        local _, _, op_pos =
            J.compare_tail(partial and tok_start or pos)
        let_rhs_operand = (op_pos == let_scope.assign_at)
    end

    -- the slot classification: via the partial's start, the trailing
    -- operand's start, or the position itself
    local sc, op_start, tail_kind, tail_kw, tail_arith = nil, nil, nil,
        nil, false
    local tail_node = nil
    if partial then
        sc = let_rhs_operand and "any" or J.slot(tok_start)
        sc = sc or pc0.slot or "any"
    elseif fresh_body then
        sc = "any"
    else
        op_start, tail_kind, tail_kw, tail_arith, tail_node =
            J.operand_tail(pos)
        sc = op_start and J.slot(op_start) or J.slot(pos)
        sc = sc or pc0.slot or "any"
    end
    if map_arrow then
        -- the map arrow's value slot is not the boolean operand the
        -- swallowed operator implies
        sc = "any"
    end
    -- the trailing operand's semantic category
    local cat = nil
    if partial then
        cat = bound_kind(partial) or "name"
    elseif tail_kind == "atom" or tail_arith then
        local ch = op_start and formula:sub(op_start, op_start) or ""
        cat = (tail_arith or ch:match("[%d%.]")) and "number" or "name"
        if cat == "name" and op_start then
            local nm = formula:sub(op_start, pos - 1):gsub("%s+$", "")
            if is_bound_name(nm) then
                cat = bound_kind(nm) or "name"
            end
        end
    elseif tail_kind == "expr" then
        cat = "group"
    elseif tail_kind == "varterm" then
        cat = "varterm"
    elseif tail_kind == "kwexpr" then
        cat = BOOLQ_KEYWORDS[tail_kw] and "boolq"
              or (VARTERM_KEYWORDS[tail_kw] and "varterm")
              or (feature_set and feature_set.dists
                  and dist_family.keywords[tail_kw] and "varterm")
              or "prob"
    elseif tail_kind == "modify" then
        cat = "modify"
    end
    -- the bool-chain walk: in a boolean operand slot, every completed
    -- operand before the current one must still be rescuable
    if sc == "bool" then
        local p = (tok_start or pos) - 1
        while true do
            while p >= 1 and is_space_byte(formula:byte(p)) do
                p = p - 1
            end
            if p < 1 then break end
            -- the separator ending just before p (whitespace aside)
            local sep, is_prefix, is_bar = nil, false, false
            local best = nil
            for _, n in ipairs(notes) do
                if n.kind ~= "oend" and n.to and n.to <= p + 1
                   and J.gap_space(n.to, p + 1) then
                    if not best or n.to > best.to then best = n end
                end
            end
            sep = best
            if sep and sep.kind == "pbar" then
                if sep.owner ~= "P" then break end
                is_bar = true
            elseif sep and sep.kind == "psep" then
                is_prefix = true
            elseif sep and sep.kind == "sep" then
                -- logical connective
            else
                break
            end
            p = sep.from - 1
            if not is_prefix then
                local os2, ok2, okw2, ohas2, onode2 = J.operand_tail(p + 1)
                if not os2 then break end
                if J.slot(os2) == "compare" then
                    -- a comparison's right side — the whole "l = r" is
                    -- boolean; continue before its left operand
                    local lstart = select(2, J.compare_tail(os2))
                    p = (lstart or os2) - 1
                elseif ohas2 or ok2 == "modify" then
                    -- an arithmetic expression or a modify result is
                    -- never boolean — under "numvar" a numeric
                    -- expression is a valid P property though
                    local operand_text = formula:sub(os2, p)
                        :gsub("%s+$", "")
                    if ohas2 and feature_set and feature_set.numvar
                       and operand_text:find("[%a_]")
                       and not operand_text:find("[%a_]%s*%(") then
                        p = os2 - 1
                    else
                        return nil
                    end
                elseif ok2 == "kwexpr" then
                    if BOOLQ_KEYWORDS[okw2] then
                        p = os2 - 1
                    elseif VARTERM_KEYWORDS[okw2] and is_bar then
                        p = os2 - 1
                    else
                        return nil
                    end
                elseif ok2 ~= "expr" then
                    local operand_text = formula:sub(os2, p)
                        :gsub("%s+$", "")
                    if not (feature_set and feature_set.marginal
                            and get_model_node_info(model,
                                                    operand_text)) then
                        return nil
                    end
                    p = os2 - 1
                else
                    p = os2 - 1
                end
            end
        end
    end

    -- a numeric operand slot (a moment argument, an arithmetic leaf)
    -- takes real-valued variables only — LET-bound names must be
    -- numeric there too, and the whole candidate list leads the offer
    local numeric_slot = pc0.owner == "MOMENT" or sc == "arith"
        or (cat == "number" and label_set.expected_numexpr ~= nil)

    local cand = identifier_candidates(env, J, pc0,
        (label_set.expected_identifier or label_set.expected_numexpr)
        and not let_rhs_operand,
        partial and tok_start or op_start)
    if let_scope then
        if let_scope.expect == "name" or let_scope.expect == "assign" then
            cand = {items = {}}
        else
            local items = cand.items or {}
            for _, nm in ipairs(let_scope.names) do
                if not numeric_slot or bound_kind(nm) == "number" then
                    items[#items + 1] = nm
                end
            end
            cand = {items = items}
        end
    end
    if sc == "arith" then
        -- the operand of ×/− must be numeric: under "numvar" a
        -- real-valued variable completes it, provided the left side is
        -- a numeric expression and not a scalar term like P(..)
        local numexpr_left = feature_set and feature_set.numvar
        if numexpr_left then
            local q = pos - 1
            while q >= 1 and is_space_byte(formula:byte(q)) do
                q = q - 1
            end
            local lstart = q >= 1 and J.operand_tail(q) or nil
            local ltext = lstart and formula:sub(lstart, q - 1) or ""
            numexpr_left = not ltext:find("[%a_]%s*%(")
        end
        if numexpr_left then
            cand = {items = numeric_var_names(model)}
        else
            cand = {items = {}}
        end
    elseif cat == "number" and label_set.expected_numexpr
           and feature_set and feature_set.numvar then
        cand = {items = numeric_var_names(model)}
    end
    if sc == "arith" or (cat == "number" and label_set.expected_numexpr) then
        if let_scope then
            local items = cand.items or {}
            for _, nm in ipairs(let_scope.names) do
                if bound_kind(nm) == "number" then
                    items[#items + 1] = nm
                end
            end
            cand = {items = items}
        end
    end

    local keywords = nil
    local suffixes = nil
    if partial then
        if let_scope then
            if let_scope.expect == "assign" then
                local out = {"="}
                -- the binding name may still be growing ("LET x" can
                -- become "LET xy"): keep the <name> marker so the
                -- letter keyboard stays up while it is being typed
                if partial and tok_start and env.let_scope_at then
                    local at = env.let_scope_at(tok_start)
                    if at and at.expect == "name" then
                        out[#out + 1] = "<name>"
                    end
                end
                return out
            elseif let_scope.expect == "name" then
                if partial == "LET" then
                    -- "LET" was just typed and a binding name is due:
                    -- a bare marker leaves the button bar empty — offer
                    -- a fresh name to tap; <name> opens the letter
                    -- keyboard for typing any other
                    local out = {}
                    local nm = let_fresh_name(env)
                    if nm then
                        out[#out + 1] = let_name_token(formula, pos, nm)
                    end
                    out[#out + 1] = "<name>"
                    return out
                end
                return nil
            end
        end
        if sc == "other" then
            if label_set.expected_let_tail
               and #partial <= 2
               and ("IN"):sub(1, #partial) == partial then
                local prev = tok_start and tok_start > 1
                    and formula:sub(tok_start - 1, tok_start - 1) or ""
                if prev:match("[%a%d_]") then
                    -- "5I"/"5IN": a digit continues into the word, so
                    -- the keyword boundary is gone — the repair is a
                    -- separated IN, spliced over the partial
                    return {" IN "}
                end
                if #partial < 2 then
                    return {("IN"):sub(#partial + 1)}
                end
            end
            return nil
        end
        cand = identifier_candidates(env, J, pc0, not let_rhs_operand,
                                     tok_start)
        if let_scope then
            if let_scope.expect == "name" or let_scope.expect == "assign" then
                cand = {items = {}}
            else
                local items = cand.items or {}
                for _, nm in ipairs(let_scope.names) do
                    if not numeric_slot or bound_kind(nm) == "number" then
                        items[#items + 1] = nm
                    end
                end
                cand = {items = items}
            end
        end
        if sc == "arith" then
            local numexpr_left = feature_set and feature_set.numvar
            if numexpr_left then
                local q = tok_start - 1
                while q >= 1 and is_space_byte(formula:byte(q)) do
                    q = q - 1
                end
                local lstart = q >= 1 and J.operand_tail(q) or nil
                local ltext = lstart and formula:sub(lstart, q - 1) or ""
                numexpr_left = not ltext:find("[%a_]%s*%(")
            end
            if numexpr_left then
                cand = {items = numeric_var_names(model)}
                if let_scope then
                    local items = cand.items
                    for _, nm in ipairs(let_scope.names) do
                        if bound_kind(nm) == "number" then
                            items[#items + 1] = nm
                        end
                    end
                end
            else
                cand = {items = {}}
                keywords = {"P("}
                for _, m in ipairs(MOMENT_STARTERS) do
                    if feature_set and feature_set[m[1]] then
                        keywords[#keywords + 1] = m[3]
                    end
                end
            end
        elseif sc == "bool" or sc == "any" then
            if label_set.expected_logical_operator
               or label_set.expected_compare or label_set.expected_lbrack
               or label_set.expected_eof then
                keywords = {}
                for _, k in ipairs(PHI_KEYWORDS) do
                    keywords[#keywords + 1] = k
                end
                for _, m in ipairs(MOMENT_STARTERS) do
                    if feature_set and feature_set[m[1]] then
                        keywords[#keywords + 1] = m[3]
                    end
                end
                if feature_set and feature_set.let then
                    keywords[#keywords + 1] = "LET"
                end
                if term_role
                   and (sc == "any" or pc0.owner == "P" or mux_term) then
                    if feature_set and feature_set.dist then
                        keywords[#keywords + 1] = "DIST("
                    end
                    if feature_set and feature_set.rename then
                        keywords[#keywords + 1] = "RENAME("
                    end
                    if feature_set and feature_set.mux then
                        keywords[#keywords + 1] = "MUX("
                    end
                    if feature_set and feature_set.dists then
                        add_pdist_keywords(keywords)
                    end
                end
            elseif label_set.expected_value or label_set.expected_psi
                   or label_set.expected_number then
                keywords = {"P("}
                for _, m in ipairs(MOMENT_STARTERS) do
                    if feature_set and feature_set[m[1]] then
                        keywords[#keywords + 1] = m[3]
                    end
                end
            end
        elseif sc == "compare" then
            if label_set.expected_value or label_set.expected_psi
               or label_set.expected_number then
                keywords = {"P("}
                for _, m in ipairs(MOMENT_STARTERS) do
                    if feature_set and feature_set[m[1]] then
                        keywords[#keywords + 1] = m[3]
                    end
                end
            end
            if pc0.brole == nil
               and (label_set.expected_logical_operator
                    or label_set.expected_compare
                    or label_set.expected_lbrack
                    or label_set.expected_eof) then
                keywords = keywords or {}
                if feature_set and feature_set.dist then
                    keywords[#keywords + 1] = "DIST("
                end
                if feature_set and feature_set.rename then
                    keywords[#keywords + 1] = "RENAME("
                end
                if feature_set and feature_set.mux then
                    keywords[#keywords + 1] = "MUX("
                end
                if feature_set and feature_set.dists then
                    add_pdist_keywords(keywords)
                end
            end
        end
        local exact = false
        suffixes = {}
        local seen_suf = {}
        local function consider(v)
            if v == partial then
                exact = true
            elseif v:sub(1, #partial) == partial then
                local suf = v:sub(#partial + 1)
                if suf ~= "" and not seen_suf[suf] then
                    seen_suf[suf] = true
                    suffixes[#suffixes + 1] = suf
                end
            end
        end
        for _, v in ipairs(cand.items or {}) do consider(tostring(v)) end
        for _, v in ipairs(keywords or {}) do consider(v) end
        if label_set.expected_let_tail then
            -- IN only completes behind a word boundary: "5I"+"N" would
            -- produce the non-keyword "5IN"
            local suf = ("IN"):sub(#partial + 1)
            if ("IN"):sub(1, #partial) == partial and suf ~= ""
               and not seen_suf[suf]
               and not (tok_start and tok_start > 1
                        and formula:sub(tok_start - 1, tok_start - 1)
                            :match("[%a%d_]")) then
                seen_suf[suf] = true
                suffixes[#suffixes + 1] = suf
            end
        end
        if not exact and not free_name_slot then
            return #suffixes > 0 and suffixes or nil
        end
    end

    -- completability drop matrices over the label set
    local drop = {}
    if mux_role == "selkey" then
        -- the key must be a selector outcome — the constrained slot
        -- dead-ends on anything else ("MUX(Intelligence, Bad " → nil)
        local dom = pc0.source and env.varterm_domain
            and env.varterm_domain(pc0.source) or nil
        if dom == nil then dom = get_model_outcomes(model) end
        local valid = {}
        for _, v in ipairs(dom or {}) do valid[tostring(v)] = true end
        if partial then
            local sufs, exact = {}, false
            for sv in pairs(valid) do
                if sv == partial then exact = true
                elseif sv:sub(1, #partial) == partial then
                    sufs[#sufs + 1] = sv:sub(#partial + 1)
                end
            end
            table.sort(sufs)
            if exact then
                local out = {"↦"}
                for _, s in ipairs(sufs) do out[#out + 1] = s end
                return out
            end
            return #sufs > 0 and sufs or nil
        end
        local nm = op_start
            and formula:sub(op_start, pos - 1):gsub("%s+$", "") or nil
        if nm ~= nil then
            return valid[nm] and {"↦"} or nil
        end
    end
    if mux_term and not pc0.in_cond then
        drop.expected_compare = true
        drop.expected_lbrack = true
        drop.expected_logical_operator = true
        if mux_role == "mixkey" then
            drop.expected_comma = true
            drop.expected_rparen = true
        end
    end
    if vc_owner and pc0.role == "mixprob" then
        -- a mixture weight is a bare probability: only the probability
        -- tokens apply, whatever the swallowed implication registered
        for l in pairs(label_set) do
            if l ~= "expected_probability" then drop[l] = true end
        end
    end
    if sc == "bool" then
        local tail_text = partial
            or (op_start and formula:sub(op_start, pos - 1)
                :gsub("%s+$", ""))
        local marginal_prop = false
        if cat == "name" and feature_set and feature_set.marginal then
            marginal_prop = get_model_node_info(model, tail_text) ~= nil
               or is_bound_name(tail_text)
        elseif cat == "number" and feature_set and feature_set.numvar then
            marginal_prop = tail_node ~= nil and numexpr_leaf(tail_node)
        end
        local numeric_tail = cat == "number"
            or numeric_name(model, tail_text)
            or bound_kind(tail_text) == "number"
        local function bool_ok(label)
            if cat == "varterm" then
                return label == "expected_compare"
                   or label == "expected_rparen"
                   or label == "expected_bar"
            end
            if cat == "name" or cat == "number" or cat == "prob" then
                if marginal_prop then
                    return label == "expected_compare"
                       or label == "expected_rparen"
                       or label == "expected_bar"
                       or (numeric_tail
                           and label == "expected_arithmetic_operator")
                end
                return label == "expected_compare"
            end
            if cat == "modify" then return false end
            return label ~= "expected_lbrack"
               and label ~= "expected_compare"
               and label ~= "expected_arithmetic_operator"
        end
        for l in pairs(label_set) do
            if not bool_ok(l) then drop[l] = true end
        end
    elseif sc == "any" then
        local function any_ok(label)
            if cat == "name" then
                local nm = partial
                    or (op_start and formula:sub(op_start, pos - 1)
                        :gsub("%s+$", ""))
                local keep_arith = feature_set and feature_set.numvar
                    and (numeric_name(model, nm)
                         or bound_kind(nm) == "number")
                return label ~= "expected_logical_operator"
                   and (keep_arith
                        or label ~= "expected_arithmetic_operator")
            end
            if cat == "varterm" then
                local numeric_lit = false
                local dom = tail_node and env.varterm_domain
                    and env.varterm_domain(tail_node)
                if type(dom) == "table" and #dom > 0 then
                    numeric_lit = true
                    for _, v in ipairs(dom) do
                        if type(v) ~= "number" then
                            numeric_lit = false
                            break
                        end
                    end
                end
                return label ~= "expected_logical_operator"
                   and (numeric_lit
                        or label ~= "expected_arithmetic_operator")
            end
            if cat == "number" or cat == "prob" then
                return label ~= "expected_logical_operator"
            end
            if cat == "boolq" then
                return label ~= "expected_compare"
                   and label ~= "expected_arithmetic_operator"
            end
            if cat == "modify" then
                return label == "expected_lbrack"
            end
            return true
        end
        for l in pairs(label_set) do
            if not any_ok(l) then drop[l] = true end
        end
    elseif sc == "arith" then
        if partial then
            for l in pairs(label_set) do drop[l] = true end
            if feature_set and feature_set.numvar then
                drop.expected_arithmetic_operator = nil
                drop.expected_compare = nil
                drop.expected_rparen = nil
                drop.expected_bar = nil
                drop.expected_eof = nil
                drop.expected_lbrack = nil
            end
        else
            drop.expected_logical_operator = true
            drop.expected_lbrack = true
        end
    elseif sc == "compare" then
        drop.expected_compare = true
        drop.expected_arithmetic_operator = true
        if feature_set and feature_set.numvar then
            local tail_name = partial
                or (op_start and formula:sub(op_start, pos - 1)
                    :gsub("%s+$", ""))
            if cat == "number"
               or (cat == "name"
                   and (numeric_name(model, tail_name)
                        or bound_kind(tail_name) == "number")) then
                drop.expected_arithmetic_operator = nil
            end
        end
        if cat == "modify" or cat == "boolq" then
            for l in pairs(label_set) do drop[l] = true end
        else
            local os = op_start or tok_start
            local rhs_ok = partial ~= nil
                or (os ~= nil
                    and formula:sub(os, pos - 1):find("[%a_]") == nil)
            local left_start = os
                and select(2, J.compare_tail(os)) or nil
            if not rhs_ok or not left_start
               or J.slot(left_start) ~= "any" then
                drop.expected_lbrack = true
            end
        end
    end
    if kw_call then
        drop.expected_lparen = nil
    end

    local result = {}
    local seen = {}
    local placeholders = {}
    local function add(s)
        if not seen[s] then
            seen[s] = true
            result[#result + 1] = s
        end
    end
    -- bound LET names lead the list wherever operands are offered: they
    -- are the formula's own locals — the most likely tap — and the
    -- bar's row cap would otherwise cut them behind the keyword flood.
    -- A numeric operand slot (moment argument, arith leaf) leads with
    -- its whole candidate list for the same reason — only real-valued
    -- variables are legal there anyway.  The candidate merge below
    -- re-adds them; `seen` keeps them once.
    if (let_scope or numeric_slot) and cand.items
       and (label_set.expected_phi or label_set.expected_identifier
            or label_set.expected_numexpr
            or label_set.expected_pdist_arg) then
        for _, v in ipairs(cand.items) do
            local nm = tostring(v)
            if is_bound_name(nm) then add(nm) end
        end
        if numeric_slot then
            for _, v in ipairs(cand.items) do add(tostring(v)) end
        end
    end
    for _, label in ipairs(labels) do
        if not drop[label] then
            local toks = label == "expected_arithmetic_operator"
                and arith_tokens(feature_set) or EXPECTED_TOKENS[label]
            if label == "expected_pdist_arg" and pc0.role == "pdist_arg" then
                toks = pc0.owner == "DEGENERATE"
                       and {"□", "<identifier>", "<number>"}
                       or {"□", "<number>"}
            end
            for _, t in ipairs(toks or {}) do
                if is_placeholder(t) then
                    placeholders[#placeholders + 1] = t
                else
                    add(t)
                end
            end
            if label == "expected_let_name" then
                -- a bare "<name>" marker alone leaves the button bar
                -- empty: offer a fresh binding name as tappable text
                -- (the letter keyboard takes any other — after it the
                -- "=" slot guides the rest step by step)
                local nm = let_fresh_name(env)
                if nm then add(let_name_token(formula, pos, nm)) end
            end
            if label == "expected_phi" or label == "expected_psi"
               or label == "expected_value" then
                for _, m in ipairs(MOMENT_STARTERS) do
                    if feature_set and feature_set[m[1]] then
                        add(m[2])
                    end
                end
            end
            if (label == "expected_phi" or label == "expected_psi")
               and feature_set and feature_set.let then
                add("LET")
            end
        end
    end
    -- variable-literal callables where a varterm is legal: the "any"
    -- root, a comparison operand, a numexpr leaf, the RENAME source
    -- slot, inside P(..) as a marginal query, a MUX term slot
    local in_bracket = pc0.brole ~= nil
    if feature_set and term_role and not in_bracket
       and (label_set.expected_phi or label_set.expected_numexpr
            or (sc == "compare" and label_set.expected_identifier)) then
        local in_p = sc == "bool" and pc0.owner == "P"
        if sc == "any" or sc == "compare" or in_p or ren_source
           or mux_term
           or (sc == "arith" and label_set.expected_numexpr) then
            if feature_set.dist then add("DIST(") end
            if feature_set.rename then add("RENAME(") end
            if feature_set.mux then add("MUX(") end
            if feature_set.dists then add_pdist_keywords(result) end
        end
    end
    -- the conditional operator continues any term
    if feature_set and feature_set.cond
       and label_set.expected_logical_operator then
        local bar_ok = cat ~= "number" and cat ~= "prob"
            and cat ~= "modify"
        if cat == "name" and sc ~= "any" and not mux_term then
            bar_ok = false
        end
        if not mux_term and (sc == "arith" or sc == "compare") then
            bar_ok = false
        end
        if bar_ok then add("|") end
    end
    if label_set.expected_phi or label_set.expected_identifier
       or label_set.expected_numexpr or label_set.expected_pdist_arg then
        for _, v in ipairs(cand.items or {}) do
            add(tostring(v))
        end
    end
    -- a word-edged token spliced at a word-char boundary must carry a
    -- separating space or it fuses into a single identifier
    -- ("Grade"+"IN" -> "GradeIN", "IN"+"X" -> "INX").  The completion
    -- suffixes below are excluded on purpose: they CONTINUE the partial
    -- under the caret ("L"+"ow" -> "Low", "I"+"N" -> "IN").
    if type(formula) == "string" then
        -- the splice may replace a span [pos, splice_to): the bytes
        -- around the SPAN are the boundary, so a token starting inside
        -- the replaced text does not count as the trailing context
        local send = env.splice_to or pos
        local before = pos > 1 and formula:sub(pos - 1, pos - 1) or ""
        local after = send <= #formula and formula:sub(send, send) or ""
        local lead = before:match("[%a%d_]") ~= nil
        local trail = after:match("[%a%d_]") ~= nil
        if lead or trail then
            for i, t in ipairs(result) do
                if lead and t:sub(1, 1):match("[%a_]") then
                    t = " " .. t
                end
                if trail and t:sub(-1):match("[%a%d_]") then
                    t = t .. " "
                end
                result[i] = t
            end
        end
    end
    for _, t in ipairs(placeholders) do
        add(t)
    end
    for _, s in ipairs(suffixes or {}) do
        add(s)
    end
    if #result == 0 then
        return nil
    end
    return result
end

-- --------------------------------------------------------------------
-- continuations for a syntactically complete formula — the AST itself
-- is the annotation: the node kind decides which operators may follow
-- --------------------------------------------------------------------

local function numeric_expected(feature_set)
    local out = {}
    for _, t in ipairs(arith_tokens(feature_set)) do
        out[#out + 1] = t
    end
    for _, t in ipairs(EXPECTED_TOKENS["expected_compare"]) do
        out[#out + 1] = t
    end
    return out
end

local function with_lbrack(list)
    local out = {}
    for _, t in ipairs(list or {}) do
        out[#out + 1] = t
    end
    out[#out + 1] = "["
    return out
end

local function ast_is_numeric(ast)
    if not ast or type(ast) ~= "table" then return false end
    local t = ast:get_type()
    if t == "value" or t == "number" then return true end
    if t ~= "operator" then return false end
    local op = ast:get_operator_name()
    if op == "prob" or MOMENT_OPS[op] or ARITH_OP_NAMES[op] then
        return true
    end
    if op == "modify_probability" then
        local inner = ast.get_child_or_nil and ast:get_child_or_nil(1)
        return inner ~= nil and ast_is_numeric(inner)
    end
    if op == "let" then
        return ast_is_numeric(ast:get_child(ast:get_num_children()))
    end
    return false
end

-- Tokens that can validly follow a complete formula AST.  env carries
-- model/features plus varterm_domain and let_scope_at/bound_kind for
-- the bound-name numeric checks.
function suggestions.continuations(ast, env)
    if not ast then return nil end
    local model, feature_set = env.model, env.features
    local formula = env.formula
    local cond_on = feature_set and feature_set.cond
    local numvar_on = feature_set and feature_set.numvar

    local function numexpr_root(node)
        return numvar_on and varterm.is_numexpr(node)
    end
    -- is this conditional term a Boolean claim or a random term?
    local function cond_is_boolean(node)
        local left = node:get_child(1)
        if left:get_type() == "identifier" then return false end
        if left:get_type() == "operator"
           and left:get_operator_name() == "conditional" then
            return cond_is_boolean(left)
        end
        return true
    end
    -- A trailing bare Boolean-domain variable is at once a complete
    -- claim and a comparison left side: "… ∧ Rain" may continue with
    -- "∧" or extend into "Rain = True".  Appends the identifier's own
    -- continuations to `out` when the claim's rightmost operand is such
    -- a name (walking nested logical chains and unary ¬).
    local function add_bare_claim_compare(out, node)
        while node and type(node) == "table"
           and node:get_type() == "operator"
           and LOGICAL_OP_NAMES[node:get_operator_name()] do
            node = node:get_child(node:get_num_children())
        end
        if not (node and node:get_type() == "identifier") then
            return out
        end
        local info = get_model_node_info(model, node:get_identifier())
        if not (info and util.is_boolean_domain(info.outcomes)) then
            return out
        end
        local seen = {}
        for _, t in ipairs(out) do seen[t] = true end
        for _, t in ipairs(
            suggestions.continuations(node, env) or {}) do
            if not seen[t] then
                out[#out + 1] = t
                seen[t] = true
            end
        end
        return out
    end
    -- is the node wrapped in parentheses?
    local paren_wrapped = false
    local npos = ast.get_positional and ast:get_positional() or nil
    if npos and type(formula) == "string" then
        local l = npos.from - 1
        while l >= 1 and formula:sub(l, l):match("%s") do l = l - 1 end
        local r = npos.to + 1
        while r <= #formula and formula:sub(r, r):match("%s") do
            r = r + 1
        end
        paren_wrapped = l >= 1 and formula:sub(l, l) == "("
            and r <= #formula and formula:sub(r, r) == ")"
    end
    if paren_wrapped then
        local t = ast:get_type()
        if t == "identifier" then
            return {"["}
        end
        if t == "value" then
            return with_lbrack(numeric_expected(feature_set))
        end
        if t == "box" then
            local out = with_lbrack(
                EXPECTED_TOKENS["expected_logical_operator"])
            for _, tk in ipairs(EXPECTED_TOKENS["expected_compare"]) do
                out[#out + 1] = tk
            end
            return out
        end
        if t ~= "operator" then
            return nil
        end
        local op0 = ast:get_operator_name()
        if op0 == "modify_probability" then
            if ast_is_numeric(ast) then
                return with_lbrack(numeric_expected(feature_set))
            end
            return with_lbrack(
                EXPECTED_TOKENS["expected_logical_operator"])
        end
        if LOGICAL_OP_NAMES[op0] or COMPARE_OP_NAMES[op0] then
            local out = with_lbrack(
                EXPECTED_TOKENS["expected_logical_operator"])
            if cond_on then out[#out + 1] = "|" end
            return out
        end
        if op0 == "conditional" then
            if cond_is_boolean(ast) then
                local out = with_lbrack(
                    EXPECTED_TOKENS["expected_logical_operator"])
                out[#out + 1] = "|"
                return out
            end
            local out = with_lbrack(EXPECTED_TOKENS["expected_compare"])
            out[#out + 1] = "|"
            return out
        end
        if BOOLQ_OPS[op0] then
            return with_lbrack(
                EXPECTED_TOKENS["expected_logical_operator"])
        end
        if VARTERM_OPS[op0] or is_pdist_op(op0) then
            local out = with_lbrack(EXPECTED_TOKENS["expected_compare"])
            if cond_on then out[#out + 1] = "|" end
            return out
        end
        if op0 == "prob" or MOMENT_OPS[op0] or ARITH_OP_NAMES[op0] then
            if numexpr_root(ast) then
                local out = with_lbrack(numeric_expected(feature_set))
                if cond_on then out[#out + 1] = "|" end
                return out
            end
            return with_lbrack(numeric_expected(feature_set))
        end
        if op0 == "let" then
            local out = {}
            for _, t in ipairs(
                EXPECTED_TOKENS["expected_logical_operator"]) do
                out[#out + 1] = t
            end
            for _, t in ipairs(numeric_expected(feature_set)) do
                out[#out + 1] = t
            end
            out[#out + 1] = "["
            if cond_on then out[#out + 1] = "|" end
            return out
        end
        return nil
    end
    if ast:get_type() == "value" then
        return with_lbrack(numeric_expected(feature_set))
    end
    if ast:get_type() == "identifier" then
        local out = with_lbrack(EXPECTED_TOKENS["expected_compare"])
        local id = ast:get_identifier()
        local numeric = numeric_name(model, id)
        if not numeric and numvar_on and feature_set
           and feature_set.let and env.let_scope_at then
            local ls = npos and env.let_scope_at(npos.to + 1) or nil
            if ls and ls.rhs then
                numeric = env.bound_kind
                    and env.bound_kind(id) == "number"
            end
        end
        if numvar_on and numeric then
            for _, t in ipairs(arith_tokens(feature_set)) do
                out[#out + 1] = t
            end
        end
        if cond_on then out[#out + 1] = "|" end
        -- a bare Boolean-domain variable is already a complete claim —
        -- Boolean connectives apply next to the comparison continuations
        local info = get_model_node_info(model, id)
        if info and util.is_boolean_domain(info.outcomes) then
            for _, t in ipairs(
                EXPECTED_TOKENS["expected_logical_operator"]) do
                out[#out + 1] = t
            end
        end
        return out
    end
    if ast:get_type() == "box" then
        local out = with_lbrack(
            EXPECTED_TOKENS["expected_logical_operator"])
        for _, t in ipairs(EXPECTED_TOKENS["expected_compare"]) do
            out[#out + 1] = t
        end
        return out
    end
    if ast:get_type() ~= "operator" then
        return nil
    end
    local op = ast:get_operator_name()
    if op == "modify_probability" then
        if ast_is_numeric(ast) then
            return with_lbrack(numeric_expected(feature_set))
        end
        return with_lbrack(EXPECTED_TOKENS["expected_logical_operator"])
    end
    if LOGICAL_OP_NAMES[op] then
        local out = {}
        for _, t in ipairs(
            EXPECTED_TOKENS["expected_logical_operator"]) do
            out[#out + 1] = t
        end
        return add_bare_claim_compare(out, ast)
    end
    if COMPARE_OP_NAMES[op] then
        local out = with_lbrack(
            EXPECTED_TOKENS["expected_logical_operator"])
        local rhs = ast:get_child(2)
        local rhs_arith = rhs and rhs:get_type() ~= "identifier"
        if not rhs_arith and numvar_on and rhs
           and rhs:get_type() == "identifier" then
            rhs_arith = numeric_name(model, rhs:get_identifier())
        end
        if rhs and varterm.is_numexpr(rhs) then rhs_arith = true end
        if rhs_arith then
            for _, t in ipairs(arith_tokens(feature_set)) do
                out[#out + 1] = t
            end
        end
        return out
    end
    if op == "let" then
        return suggestions.continuations(
            ast:get_child(ast:get_num_children()), env)
    end
    if BOOLQ_OPS[op] then
        return with_lbrack(EXPECTED_TOKENS["expected_logical_operator"])
    end
    if op == "conditional" then
        -- the condition's trailing operand may be a bare Boolean-domain
        -- variable that can still extend into a comparison
        -- ("X | Bronchitis" -> "X | Bronchitis = yes")
        local cond = ast:get_child(ast:get_num_children())
        if cond_is_boolean(ast) then
            local out = with_lbrack(
                EXPECTED_TOKENS["expected_logical_operator"])
            out[#out + 1] = "|"
            return add_bare_claim_compare(out, cond)
        end
        return add_bare_claim_compare({"[", "|"}, cond)
    end
    if VARTERM_OPS[op] or is_pdist_op(op) then
        local out = with_lbrack(EXPECTED_TOKENS["expected_compare"])
        if numvar_on and env.varterm_domain then
            local dom = env.varterm_domain(ast)
            if type(dom) == "table" and #dom > 0 then
                local allnum = true
                for _, v in ipairs(dom) do
                    if type(v) ~= "number" then
                        allnum = false
                        break
                    end
                end
                if allnum then
                    for _, t in ipairs(arith_tokens(feature_set)) do
                        out[#out + 1] = t
                    end
                end
            end
        end
        if cond_on then out[#out + 1] = "|" end
        return out
    end
    if op == "prob" or MOMENT_OPS[op] or ARITH_OP_NAMES[op] then
        if numexpr_root(ast) then
            local out = with_lbrack(numeric_expected(feature_set))
            if cond_on then out[#out + 1] = "|" end
            return out
        end
        return with_lbrack(numeric_expected(feature_set))
    end
    return nil
end

-- --------------------------------------------------------------------
-- suffix completions for a partially typed token (kept for the service
-- layer's caret-merge path)
-- --------------------------------------------------------------------

local MATCH_FORM = {["ℙ("] = "P(", ["𝒫("] = "P(", ["𝔼("] = "E(", ["𝕍("] = "VAR(",
                    ["σ("] = "SD(", ["↦"] = "->", ["¬"] = "!",
                    ["∧"] = "&&", ["∨"] = "||", ["→"] = "->",
                    ["↔"] = "<->", ["≤"] = "<=", ["≥"] = ">=",
                    ["×"] = "*", ["−"] = "-", ["÷"] = "/",
                    ["↑"] = "nand", ["↓"] = "nor", ["⊕"] = "xor"}
function suggestions.partial_suffixes(tokens, partial)
    local out, seen = {}, {}
    for _, t in ipairs(tokens or {}) do
        -- resolve() pads word-edged tokens at word boundaries; the pad
        -- is a splice detail, not part of the candidate's text
        if type(t) == "string" then t = t:match("^%s*(.-)%s*$") end
        if is_placeholder(t) then goto continue end
        local match = MATCH_FORM[t] or t
        if #match > #partial and match:sub(1, #partial) == partial
           and not seen[match] then
            seen[match] = true
            out[#out + 1] = match:sub(#partial + 1)
        elseif #t > #partial and t:sub(1, #partial) == partial
               and not seen[t] then
            seen[t] = true
            out[#out + 1] = t:sub(#partial + 1)
        end
        ::continue::
    end
    return out
end

suggestions.node_cat = node_cat
suggestions.bool_completable = bool_completable
suggestions.numeric_completable = numeric_completable
suggestions.termish_completable = termish_completable
suggestions.term_completable = term_completable
suggestions.MATCH_FORM = MATCH_FORM
suggestions.MOMENTS = {"𝔼(", "𝕍(", "σ("}
suggestions.MOMENT_OPS = MOMENT_OPS
suggestions.MOMENT_STARTERS = MOMENT_STARTERS
suggestions.PHI_KEYWORDS = PHI_KEYWORDS
suggestions.VARTERM_CALLABLES = {"DIST(", "RENAME(", "MUX("}
suggestions.last_identifier_before = last_identifier_before
suggestions.is_placeholder = is_placeholder

return suggestions
