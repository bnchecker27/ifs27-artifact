--- English explanation of a parsed BayesL formula.
--
-- The explainer walks the formula AST produced by logic.parser_bn_logic and
-- produces a cdecl-like plain-English sentence that describes what the
-- formula means.  It uses the same AST that the model checker consumes and
-- optionally the BN information (variable/value tables) to disambiguate
-- identifiers that are variables from identifiers that are node values.
--
-- In addition to the plain English sentence, the explainer can produce a
-- list of segments that link each contiguous fragment of the explanation
-- back to the byte range of the AST subformula it describes.  This is used
-- for hover/click cross-highlighting between the formula and its explanation
-- in the UI.

local logic = require("logic.logic")
local dist_family = require("logic.dist_family")

local explainer = {}

-- ---------------------------------------------------------------------------
-- helpers

local function is_formula(x)
    return type(x) == "table" and x.is_formula
end

local function classify(name, info)
    if not info then
        return "name"
    end
    if name == "true" or name == "false" then
        return "boolean"
    end
    if info.variables and info.variables[name] then
        return "variable"
    end
    if info.all_values and info.all_values[name] then
        return "value"
    end
    return "name"
end

local function simple_name(ast, info)
    if logic.is_identifier(ast) then
        local n = ast:get_identifier()
        return n
    elseif logic.is_value(ast) then
        return tostring(ast:get_value())
    end
    return nil
end

local function is_simple(ast)
    return logic.is_identifier(ast) or logic.is_value(ast)
end

local function is_boolean_literal(ast)
    return logic.is_identifier(ast)
           and (ast:get_identifier() == "true" or ast:get_identifier() == "false")
end

-- Decide whether the child expression needs parentheses when it appears
-- inside the parent operator.  The same idea as logic.lua's child_needs_braces
-- but adapted for English text.
local function needs_wrap(parent_op, child)
    if not parent_op then
        return false
    end
    if not logic.is_operator(child) then
        return false
    end
    local cop = child:get_operator()
    if not cop then
        return false
    end
    if parent_op.name == "not" and logic.is_operator(child) then
        -- "not X is 0" is ambiguous, so parenthesise any operator operand.
        return true
    end
    -- A comparison (an atom/event) is a self-contained English phrase and
    -- does not need parentheses when it is the argument of a quantifier.
    -- MAP and MPE are also event-returning quantifiers and read naturally
    -- as events inside P(...).
    if parent_op.precedence >= 7 then
        local copname = cop.name
        if copname == "less" or copname == "less_or_equal" or copname == "equal"
           or copname == "greater_or_equal" or copname == "greater"
           or copname == "map" or copname == "mpe" then
            return false
        end
    end
    if parent_op.precedence < cop.precedence then
        return false
    end
    if parent_op.precedence > cop.precedence then
        return true
    end
    -- same precedence
    if parent_op.name == cop.name and parent_op.associative and cop.associative then
        return false
    end
    return true
end

-- ---------------------------------------------------------------------------
-- annotation state

-- A "state" is a list of text pieces, each carrying the AST node whose
-- formula byte range the piece describes.  Parentheses and grammatical
-- glue are attached to the parent AST so hovering them highlights the
-- whole parent formula; child words carry the child AST so the innermost
-- subformula is preferred.

local function new_state()
    return { parts = {}, pos = 0 }
end

local function append(state, text, ast)
    if not text or text == "" then
        return
    end
    table.insert(state.parts, { text = text, ast = ast })
    state.pos = state.pos + #text
end

local function append_state(dst, src)
    for _, p in ipairs(src.parts) do
        table.insert(dst.parts, p)
    end
    dst.pos = dst.pos + src.pos
end

local function state_text(state)
    local out = {}
    for _, p in ipairs(state.parts) do
        out[#out + 1] = p.text
    end
    return table.concat(out)
end

-- Mutually recursive builders for the AST; the actual functions are
-- assigned after this forward declaration.
local build, build_wrapped

-- Build the child into a state, optionally prefixing with "the value of "
-- for variables, and wrapping in parentheses when needed.
build_wrapped = function(child, info, parent_op, parent_ast, prefix)
    local child_state = build(child, info)
    if prefix then
        local pre = new_state()
        append(pre, prefix, parent_ast)
        append_state(pre, child_state)
        child_state = pre
    end
    if needs_wrap(parent_op, child) then
        local out = new_state()
        append(out, "(", parent_ast)
        append_state(out, child_state)
        append(out, ")", parent_ast)
        return out
    end
    return child_state
end

-- ---------------------------------------------------------------------------
-- identifier lists

-- Append a comma-separated identifier list, one segment per identifier,
-- so each sentence part maps to exactly one contiguous formula range.
-- The connecting words/commas attach to the parent operator.
local function append_name_list(state, list, parent)
    if not list or #list == 0 then
        return
    end
    local n = #list
    for i = 1, n do
        local item = list[i]
        local ast = (type(item) == "table" and item.get_positional)
                    and item or parent
        append(state, tostring(item), ast)
        if i == n - 1 then
            append(state, " and ", parent)
        elseif i < n then
            append(state, ", ", parent)
        end
    end
end

-- ---------------------------------------------------------------------------
-- sorted table helpers

local function sorted_keys(t)
    local keys = {}
    if type(t) == "table" then
        for k, _ in pairs(t) do
            keys[#keys + 1] = tostring(k)
        end
    end
    table.sort(keys)
    return keys
end

-- ---------------------------------------------------------------------------
-- build functions

local function build_compare(state, ast, info, op)
    local c1, c2 = ast:get_child(1), ast:get_child(2)

    -- Equality of a variable and a value/variable/boolean can be phrased
    -- naturally (the most common atom in the language).
    if op.name == "equal" and is_simple(c1) and is_simple(c2) then
        local n1 = simple_name(c1, info)
        local n2 = simple_name(c2, info)
        if n1 and n2 then
            local c1_var = logic.is_identifier(c1)
                           and classify(c1:get_identifier(), info) == "variable"
            local c2_var = logic.is_identifier(c2)
                           and classify(c2:get_identifier(), info) == "variable"
            -- Put the variable on the left for naturalness ("X is 0" not "0 is X").
            if c2_var and not c1_var then
                append(state, n2, c2)
                append(state, " is ", ast)
                append(state, n1, c1)
            else
                append(state, n1, c1)
                append(state, " is ", ast)
                append(state, n2, c2)
            end
            return
        end
    end

    local p1 = ""
    if logic.is_identifier(c1) and classify(c1:get_identifier(), info) == "variable" then
        p1 = "the value of "
    end
    local p2 = ""
    if logic.is_identifier(c2) and classify(c2:get_identifier(), info) == "variable" then
        p2 = "the value of "
    end

    append_state(state, build_wrapped(c1, info, op, ast, p1 ~= "" and p1 or nil))
    append(state, " ", ast)

    local verb = ({
        less             = "is less than",
        less_or_equal    = "is less than or equal to",
        equal            = "is equal to",
        greater_or_equal = "is greater than or equal to",
        greater          = "is greater than",
    })[op.name] or ("is " .. (op.default_symbol or op.name) .. " ")
    append(state, verb, ast)

    append(state, " ", ast)
    append_state(state, build_wrapped(c2, info, op, ast, p2 ~= "" and p2 or nil))
end

build = function(ast, info, standalone)
    local state = new_state()

    if not is_formula(ast) then
        return state
    end

    local t = ast:get_type()

    if t == "identifier" then
        -- a standalone bare variable name is a marginal-distribution
        -- query — "Grade" explains as "the distribution of Grade".
        -- Nested identifiers keep the plain name ("the value of" is
        -- added by build_compare where appropriate).
        local name = ast:get_identifier()
        if standalone and classify(name, info) == "variable" then
            append(state, "the distribution of ", ast)
            append(state, name, ast)
        else
            append(state, name, ast)
        end
        return state
    end

    if t == "value" then
        append(state, tostring(ast:get_value()), ast)
        return state
    end

    if t ~= "operator" then
        append(state, tostring(ast), ast)
        return state
    end

    local op = ast:get_operator()
    local name = op and op.name or ""

    -- comparison / atom
    if name == "less" or name == "less_or_equal" or name == "equal"
       or name == "greater_or_equal" or name == "greater" then
        build_compare(state, ast, info, op)
        return state
    end

    -- logical connectives
    if name == "not" then
        append(state, "not ", ast)
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        return state
    end

    if name == "and" then
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " and ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    if name == "or" then
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " or ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    if name == "nand" then
        append(state, "not both ", ast)
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " and ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    if name == "nor" then
        append(state, "neither ", ast)
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " nor ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    if name == "implication" then
        append(state, "if ", ast)
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " then ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    if name == "biimplication" then
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " if and only if ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    if name == "xor" then
        append(state, "either ", ast)
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " or ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        append(state, ", but not both", ast)
        return state
    end

    -- arithmetic
    if name == "times" then
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " times ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    if name == "plus" then
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " plus ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    if name == "divide" then
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " divided by ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    if name == "minus" then
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " minus ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    -- probability quantifier
    if name == "prob" then
        local n = ast:get_num_children()
        local event = ast:get_child(1)
        append(state, "the probability that ", ast)
        append_state(state, build_wrapped(event, info, op, ast))
        if n >= 2 then
            local cond = ast:get_child(2)
            append(state, " given that ", ast)
            append_state(state, build_wrapped(cond, info, op, ast))
        end
        return state
    end

    -- moment queries: expectation, variance and standard deviation of
    -- a random variable (the "expect"/"variance"/"sd" features)
    if name == "expect" or name == "variance" or name == "sd" then
        append(state, name == "expect" and "the expectation of "
                  or name == "variance" and "the variance of "
                  or "the standard deviation of ", ast)
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        return state
    end

    -- most likely partial assignment
    if name == "map" then
        local n = ast:get_num_children()
        local has_cond = op.has_condition or false
        local n_names = n - (has_cond and 1 or 0)
        local cond = has_cond and ast:get_child_or_nil(n) or nil
        append(state, "the most likely values of ", ast)
        local id_nodes = {}
        for i = 1, n_names do
            table.insert(id_nodes, ast:get_child(i))
        end
        append_name_list(state, id_nodes, ast)
        if cond and not is_boolean_literal(cond) then
            append(state, " given that ", ast)
            append_state(state, build_wrapped(cond, info, op, ast))
        end
        return state
    end

    -- most likely complete assignment
    if name == "mpe" then
        local n = ast:get_num_children()
        local cond = n > 0 and ast:get_child(1) or nil
        if cond and not is_boolean_literal(cond) then
            append(state, "the most likely assignment to all non-evidence variables given that ", ast)
            append_state(state, build_wrapped(cond, info, op, ast))
        else
            append(state, "the most likely assignment to all variables", ast)
        end
        return state
    end

    -- conditional independence
    if name == "idp" then
        local left = ast:get_child_or_nil(1)
        local right = ast:get_child_or_nil(2)
        local cond = {}
        for i = 3, ast:get_num_children() do
            table.insert(cond, ast:get_child(i))
        end
        append(state, tostring(left), left)
        append(state, " and ", ast)
        append(state, tostring(right), right)
        append(state, " are conditionally independent", ast)
        if #cond > 0 then
            append(state, " given ", ast)
            append_name_list(state, cond, ast)
        else
            append(state, " (marginally)", ast)
        end
        return state
    end

    if name == "infl" then
        local left = ast:get_child_or_nil(1)
        local right = ast:get_child_or_nil(2)
        local cond = {}
        for i = 3, ast:get_num_children() do
            table.insert(cond, ast:get_child(i))
        end
        append(state, tostring(left), left)
        append(state, " and ", ast)
        append(state, tostring(right), right)
        append(state, " are not conditionally independent", ast)
        if #cond > 0 then
            append(state, " given ", ast)
            append_name_list(state, cond, ast)
        else
            append(state, " (marginally)", ast)
        end
        append(state, " -- there is an active trail", ast)
        return state
    end

    -- CPT update
    if name == "modify_probability" then
        local inner = ast:get_child_or_nil(1)
        append(state, "the value of ", ast)
        if inner then
            append_state(state, build_wrapped(inner, info, op, ast))
        else
            append(state, "the formula", ast)
        end
        append(state, " under the intervention that ", ast)

        local target = ast:get_child_or_nil(2)
        local prob_count = op.prob_map_count or 0
        local cond_count = op.condition_count or 0
        local prob_map_children = {}
        local condition_children = {}
        for i = 3, 2 + prob_count do
            local c = ast:get_child_or_nil(i)
            if c then table.insert(prob_map_children, c) end
        end
        for i = 3 + prob_count, 2 + prob_count + cond_count do
            local c = ast:get_child_or_nil(i)
            if c then table.insert(condition_children, c) end
        end

        if target then
            append(state, "the probability of ", ast)
            append_state(state, build_wrapped(target, info, op, ast))
            append(state, " being ", ast)
        else
            append(state, "the probability of the intervention", ast)
        end

        for i, map_child in ipairs(prob_map_children) do
            append_state(state, build_wrapped(map_child, info, op, ast))
            if i < #prob_map_children then
                append(state, " and ", ast)
            end
        end

        if #condition_children > 0 then
            append(state, " given ", ast)
            for i, cond_child in ipairs(condition_children) do
                append_state(state, build_wrapped(cond_child, info, op, ast))
                if i < #condition_children then
                    append(state, " and ", ast)
                end
            end
        end
        return state
    end

    -- a named distribution literal ("dists" feature): a fresh variable
    -- with the family's support, independent of the model — the
    -- arguments are literals, rendered bare
    if dist_family.specs[name] then
        append(state, "the independent "
                      .. dist_family.specs[name].kw:lower()
                      .. " distribution (", ast)
        for i = 1, ast:get_num_children() do
            if i > 1 then
                append(state, ", ", ast)
            end
            append_state(state, build_wrapped(ast:get_child(i), info, op, ast))
        end
        append(state, ")", ast)
        return state
    end

    -- DIST literal: a fresh variable declared by its
    -- outcome→probability map, independent of the model
    if name == "dist" then
        append(state, "the independent distribution ", ast)
        for i = 1, ast:get_num_children() do
            if i > 1 then
                append(state, ", ", ast)
            end
            append_state(state, build_wrapped(ast:get_child(i), info, op, ast))
        end
        return state
    end

    -- RENAME: a dependent variable g(source) — the source term with
    -- its outcomes renamed by the map entries
    if name == "rename" then
        append(state, "the renaming of ", ast)
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " where ", ast)
        for i = 2, ast:get_num_children() do
            if i > 2 then
                append(state, ", ", ast)
            end
            append_state(state, build_wrapped(ast:get_child(i), info, op, ast))
        end
        return state
    end

    -- MUX: selector form "MUX(S, o ↦ X, …)" picks the branch variable
    -- whose entry key matches the selector's outcome; the mixture
    -- "MUX(X ↦ p, …)" picks branch i with weight pᵢ
    if name == "mux" then
        local c1 = ast:get_child_or_nil(1)
        local mixture = c1 and c1:get_type() == "operator"
                      and c1:get_operator_name() == "equal"
                      and c1:get_child_or_nil(2)
                      and c1:get_child(2):get_type() == "value"
        if mixture then
            append(state, "the mixture of ", ast)
            for i = 1, ast:get_num_children() do
                if i > 1 then
                    append(state, ", ", ast)
                end
                append_state(state, build_wrapped(ast:get_child(i), info, op, ast))
            end
        else
            append(state, "the multiplexing of ", ast)
            append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
            append(state, " into ", ast)
            for i = 2, ast:get_num_children() do
                if i > 2 then
                    append(state, ", ", ast)
                end
                append_state(state, build_wrapped(ast:get_child(i), info, op, ast))
            end
        end
        return state
    end

    -- LET bindings ("let" feature): "with X = …, the body" — each
    -- binding child renders "X = its right side"
    if name == "let" then
        local n = ast:get_num_children()
        append(state, "with ", ast)
        for i = 1, n - 1 do
            if i > 1 then
                append(state, " and ", ast)
            end
            append_state(state, build_wrapped(ast:get_child(i), info, op, ast))
        end
        append(state, ", ", ast)
        append_state(state, build_wrapped(ast:get_child(n), info, op, ast))
        return state
    end
    if name == "binding" then
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " bound to ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    end

    -- conditional term/event ("term | claim"): a conditioned variable
    -- asks for a conditional distribution, a conditioned claim is a
    -- conditional event
    if name == "conditional" then
        local left = ast:get_child_or_nil(1)
        local right = ast:get_child_or_nil(2)
        if left and left:get_type() == "identifier" then
            append(state, "the conditional distribution of ", ast)
            append_state(state, build_wrapped(left, info, op, ast))
        elseif left then
            append_state(state, build_wrapped(left, info, op, ast))
        end
        if right then
            append(state, " given that ", ast)
            append_state(state, build_wrapped(right, info, op, ast))
        end
        return state
    end

    -- fallback: operator symbol in infix/postfix/prefix notation
    local n = ast:get_num_children()
    if n == 1 then
        local inner = ast:get_child(1)
        local inner_state = build_wrapped(inner, info, op, ast)
        if op.notation == "prefix" then
            append(state, op.default_symbol or name, ast)
            append(state, " ", ast)
            append_state(state, inner_state)
        else
            append_state(state, inner_state)
            append(state, " ", ast)
            append(state, op.default_symbol or name, ast)
        end
        return state
    elseif n == 2 then
        append_state(state, build_wrapped(ast:get_child(1), info, op, ast))
        append(state, " ", ast)
        append(state, op.default_symbol or name, ast)
        append(state, " ", ast)
        append_state(state, build_wrapped(ast:get_child(2), info, op, ast))
        return state
    else
        append(state, tostring(ast), ast)
        return state
    end
end

-- ---------------------------------------------------------------------------
-- public API

function explainer.explain(ast, info)
    return state_text(build(ast, info, true))
end

function explainer.explain_segments(ast, info)
    local state = build(ast, info, true)
    local text = state_text(state)
    local segments = {}
    local pos = 0
    for _, p in ipairs(state.parts) do
        local from, to
        if p.ast and p.ast.get_positional then
            local posi = p.ast:get_positional()
            if posi then
                from = posi.from
                to = posi.to
            end
        end
        table.insert(segments, {
            text = p.text,
            explanation_from = pos + 1,
            explanation_to = pos + #p.text,
            formula_from = from,
            formula_to = to,
        })
        pos = pos + #p.text
    end
    return { text = text, segments = segments }
end

return explainer
