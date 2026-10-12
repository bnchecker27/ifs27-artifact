---
---

local lpeg = require "lpeg"
local lpeg_util = require "lib.lpeg_util"
local parsing_context = require "lib.parsing_context"
local logic = require "logic.logic"
local make_positional = require "lib.positional"

local Space = lpeg.S(" \n\t")^0
local Open = "(" * Space
local Close = ")" * Space

local function map_operators_to_precedence(operators)
    local by_precedence = {}
    for _,operator in ipairs(operators) do
        local precedence = operator.precedence
        local precedence_operators = by_precedence[precedence]
        if not precedence_operators then
            precedence_operators = {}
            by_precedence[precedence] = precedence_operators
        end
        table.insert(precedence_operators, operator)
    end
    return by_precedence
end

local function compute_all_precedences(by_precedence)
    local all_precedences = {}
    for precedence,_ in pairs(by_precedence) do
        table.insert(all_precedences, precedence)
    end
    table.sort(all_precedences)
    return all_precedences
end

local function compute_precedence_vars(all_precedences, name)
    local prefix = name .. "_"
    local precedence_names = {}
    local prececence_vars = {}
    for _, precedence in ipairs(all_precedences) do
        local precedence_name = string.format("%slevel_%f", prefix, precedence)
        local precedence_var = lpeg.V(precedence_name)
        precedence_names[precedence] = precedence_name
        prececence_vars[precedence] = precedence_var
    end
    return precedence_names, prececence_vars
end

local function compute_precedence_operators(all_precedences, by_precedence, operator_symbol_parsers)
    local all_operators = {}
    for _, precedence in ipairs(all_precedences) do
        local precedence_operators = by_precedence[precedence]
        local precedence_term = lpeg.P(false)
        for _, operator in ipairs(precedence_operators) do
            local op_term
            if operator.symbols then
                op_term = lpeg_util.string_array_S(operator.symbols, function() return operator end) * Space
            else
                op_term = operator_symbol_parsers[operator.name]
            end
            if op_term then
                precedence_term = precedence_term + op_term
            end
        end
        all_operators[precedence] = precedence_term
    end
    return all_operators
end

-- one op's symbol parser, mirroring compute_precedence_operators but
-- keeping the operators separate so operand annotations can attach per
-- operator (boolean connectives suppress varterm offers in their
-- operand; the conditional "|" does not).  The op token journals a
-- separator note before its trailing Space so the resolver's operand
-- chain walk sees the operator, not the whitespace.
local function operator_term(operator, operator_symbol_parsers)
    if operator.symbols then
        -- the symbol text is captured too: the separator note records
        -- it (`->` doubles as a map/comparison arrow in the resolver's
        -- operand-chain queries while `→` does not)
        local toks = lpeg.P(false)
        for _, sym in ipairs(operator.symbols) do
            toks = toks + lpeg.C(lpeg.P(sym))
        end
        if operator.sep_kind then
            toks = lpeg_util.sep_note(toks, operator.sep_kind,
                function(_, sym)
                    return {cls = operator.csep_cls,
                            nslot = operator.rhs_slot,
                            sym = sym}
                end)
        end
        return toks * Space / function() return operator end
    end
    return operator_symbol_parsers[operator.name]
end

-- suggestion payloads for a precedence layer's operators: each
-- operator's offerable symbol at a continuation/operand position
local function operator_suggest(ops)
    local symbols = {}
    for _, op in ipairs(ops) do
        symbols[#symbols + 1] = op.default_symbol or op.suggest_symbol
    end
    return {kind = "ops", symbols = symbols}
end

-- the continuation variant: carries the layer's operand requirement
-- (left_needs — e.g. a boolean connective's operand must be a claim)
-- and the AST of the operand being continued, bound by track() to
-- "sug_after".  The resolver drops the symbols when the operand cannot
-- satisfy the requirement.
local function operator_suggest_cont(ops)
    local symbols = {}
    for _, op in ipairs(ops) do
        symbols[#symbols + 1] = op.default_symbol or op.suggest_symbol
    end
    local needs = ops[1] and ops[1].left_needs
    return function(after)
        return {kind = "ops", symbols = symbols,
                needs = needs, after = after}
    end
end

local function compute_next_layer_var(number, all_precedences, prececence_vars, level_last_name)
    local next_layer_var
    local precedence = all_precedences[number]
    if precedence < all_precedences[#all_precedences] then
        local next_precedence = all_precedences[number + 1]
        next_layer_var = prececence_vars[next_precedence]
    else
        next_layer_var = lpeg.V(level_last_name)
    end
    return next_layer_var
end

local function new_lists(pos_1, start_term, pos_2)
    pos_2 = pos_2 - 1
    local result = {}
    result.operators = {}
    result.terms = {}
    result.positions = {}
    result.positions = {}
    table.insert(result.terms, start_term)
    table.insert(result.positions, pos_1)
    table.insert(result.positions, pos_2)
    return result
end

local function add_to_list(lists,  operator, pos_1, term, pos_2)
--    pos_1 = pos_1 - 1
    pos_2 = pos_2 - 1
    table.insert(lists.operators, operator)
    table.insert(lists.terms, term)
    table.insert(lists.positions, pos_1)
    table.insert(lists.positions, pos_2)
    return lists
end

local function handle_last_layer(result, auxiliary)
    local all_precedences = auxiliary.all_precedences
    local prececence_vars = auxiliary.prececence_vars
    local aps = auxiliary.aps
    local first_precedence = all_precedences[1]
    local first_var = prececence_vars[first_precedence]
    local expected = auxiliary.context:Label("expected_" .. auxiliary.name)
    local CloseOrError = lpeg_util.labeled(Close, "expected_rparen",
                                           {kw = ")"})
    -- a parenthesised group: its operand is transparent (the "(x)" node
    -- is x itself) but its interior is a fresh "any" operand even in a
    -- compare-rhs context — "A = (…)" opens a self-contained formula —
    -- so the scope overrides slot "compare" back to "any" and clears
    -- the enclosing paren's owner (paren_context inside "(…)" reports
    -- no keyword).
    local group = Open * lpeg_util.sug_scope(first_var, {
        owner = false,
        in_p = false,
        slot = function(e)
            if e and e.slot == "compare" then return "any" end
        end})
    local next_layer = lpeg_util.track(aps)
                     + lpeg_util.suggestable(
                         lpeg_util.track(lpeg_util.marked(
                             group * CloseOrError, "expr")),
                         {kw = "("})
                     + expected
    result[auxiliary.level_last_name] = next_layer
end

local function compute_auxiliary(parameters)
    local by_precedence = map_operators_to_precedence(parameters.operators)
    local all_precedences = compute_all_precedences(by_precedence)
    local name = parameters.name or "p"
    local level_last_name = name .. "_level_last"
    local precedence_names, prececence_vars = compute_precedence_vars(all_precedences, name)
    local by_precedence_ops = compute_precedence_operators(all_precedences, by_precedence, parameters.operator_symbol_parsers)
    local result = {
        operators=parameters.operators,
        aps=parameters.aps,
        context=parameters.context,
        operator_symbol_parsers=parameters.operator_symbol_parsers,
        operator_parsers=parameters.operator_parsers,
        infix_label=parameters.infix_label,
        postfix_label=parameters.postfix_label,
        by_precedence=by_precedence,
        all_precedences=all_precedences,
        precedence_names=precedence_names,
        prececence_vars=prececence_vars,
        by_precedence_ops=by_precedence_ops,
        name=name,
        level_last_name=level_last_name
    }
    return result
end

local function compute_layer_aux(auxiliary, number)
    local precedence = auxiliary.all_precedences[number]
    local precedence_ops = auxiliary.by_precedence_ops[precedence]
    local this_layer = auxiliary.prececence_vars[precedence]
    local next_layer_var = compute_next_layer_var(number, auxiliary.all_precedences, auxiliary.prececence_vars, auxiliary.level_last_name)
    local sample_op = auxiliary.by_precedence[precedence][1]
    local precedence_var_name = auxiliary.precedence_names[precedence]
    local result = {
        precedence = precedence,
        precedence_ops = precedence_ops,
        this_layer = this_layer,
        next_layer_var = next_layer_var,
        sample_op = sample_op,
        precedence_var_name = precedence_var_name
    }
    return result
end

local function handle_binary_infix_layer(result, auxiliary, number)
    local function combine_lists_left(lists)
        local result = lists.terms[1]
        local pos_from = lists.positions[1]
        for i,operator in ipairs(lists.operators) do
            local pos_to = lists.positions[2*i + 2]
            local term = lists.terms[i+1]
            local positional = make_positional(auxiliary.context.input, pos_from, pos_to)
            result = logic.make_binary_operator(result, term, operator, positional)
        end
        return result
    end

    local function combine_lists_right(lists)
        local result = lists.terms[#lists.terms]
        local pos_to = lists.positions[#lists.positions]
        for i=1,#lists.operators,1 do
            local operator = lists.operators[#lists.operators-i+1]
            local term = lists.terms[#lists.terms-i]
            local pos_from = lists.positions[#lists.positions - 1 - 2*i]
            local positional = make_positional(auxiliary.context.input, pos_from, pos_to)
            result = logic.make_binary_operator(term, result, operator, positional)
        end
        return result
    end

    local layer_aux = compute_layer_aux(auxiliary, number)
    local context = auxiliary.context
    local expected = context:Label("expected_" .. auxiliary.name)

    -- when the operator symbols do not match, the repetition ends
    -- legitimately — but the operator position is still a valid
    -- continuation, so it is labelled for the expected-token machinery.
    -- (The label sits in a non-consuming suffix: a Cmt inside the ^0 body
    -- would make LPeg reject the loop as possibly-empty.)
    -- The op alternatives are unmerged so an operator can annotate its
    -- operand slot (operand_suppress): the record registers at the
    -- operand's own failure position — farther failures discard it.
    local op_tail = lpeg.P(false)
    local ops = auxiliary.by_precedence[layer_aux.precedence]
    for _, op in ipairs(ops) do
        local op_term = operator_term(op, auxiliary.operator_symbol_parsers)
        if op_term then
            local operand = layer_aux.next_layer_var
            if op.operand_suppress then
                operand = operand + parsing_context.Suggest(nil,
                    {suppress = op.operand_suppress})
            end
            -- the operand's slot: a boolean connective's rhs is a
            -- "bool" position, an arithmetic op's "arith" — payloads
            -- and operand-end notes inside carry the stamp
            if op.rhs_slot then
                operand = lpeg_util.sug_scope(operand,
                                              {slot = op.rhs_slot,
                                               cond = op.rhs_in_cond})
            end
            op_tail = op_tail + (op_term * context:Cp() * operand
                                 * context:Cp())
        end
    end
    local with_op = context:Cp() * layer_aux.next_layer_var * context:Cp() / new_lists * (op_tail % add_to_list)^0
    if layer_aux.sample_op.associativity == "left" then
        with_op = with_op / combine_lists_left
    elseif layer_aux.sample_op.associativity == "right" then
        with_op = with_op / combine_lists_right
    else
        error()
    end
    -- bind the folded operand before the continuation annotations run:
    -- Cb("sug_after") inside them then yields this layer's operand node
    with_op = lpeg.Cg(with_op, "sug_after") * lpeg.Cb("sug_after")
    if auxiliary.infix_label then
        with_op = with_op * (context:Label(auxiliary.infix_label)
                             + parsing_context.Suggest(
                                 lpeg.Cb("sug_after") + lpeg.Cc(nil),
                                 operator_suggest_cont(ops))
                             + lpeg.P(true))
    end
    result[layer_aux.precedence_var_name] = with_op + expected
end

local function handle_unary_prefix_layer(result, auxiliary, number)
    local function make_unary_operator_prefix(pos_from, operator, inner, pos_to)
        assert(operator)
        assert(inner)
        pos_to = pos_to - 1
        local positional = make_positional(auxiliary.context.input, pos_from, pos_to)
        if operator.make_operator then
            return operator.make_operator(inner, positional)
        end
        return logic.make_unary_operator(inner, operator, positional)
    end

    local layer_aux = compute_layer_aux(auxiliary, number)
    local context = auxiliary.context
    local expected = context:Label("expected_" .. auxiliary.name)
    -- per-operator alternatives: the prefix symbol's own position is
    -- offerable at every operand start ("¬" is a legal formula starter),
    -- and an op may suppress offer categories inside its operand
    -- (boolean negation drops varterm callables).
    local ops = auxiliary.by_precedence[layer_aux.precedence]
    local op_prefixed = lpeg.P(false)
    for _, op in ipairs(ops) do
        local op_term = operator_term(op, auxiliary.operator_symbol_parsers)
        if op_term then
            local operand = layer_aux.this_layer
            if op.operand_suppress then
                operand = operand + parsing_context.Suggest(nil,
                    {suppress = op.operand_suppress})
            end
            if op.rhs_slot then
                operand = lpeg_util.sug_scope(operand,
                                              {slot = op.rhs_slot})
            end
            op_prefixed = op_prefixed + (op_term * operand)
        end
    end
    local with_op = lpeg_util.track(layer_aux.next_layer_var)
                  + lpeg_util.track(
                        context:Cp()
                        * (op_prefixed
                           + parsing_context.Suggest(nil,
                               operator_suggest(ops)))
                        * context:Cp()
                        / make_unary_operator_prefix)
                  + expected
    result[layer_aux.precedence_var_name] = with_op
end

local function handle_unary_postfix_layer(result, auxiliary, number)
    local pos_from

    local function make_unary_operator_postfix(inner, operator, pos_to)
        assert(operator)
        assert(inner)
        pos_to = pos_to - 1
        local positional = make_positional(auxiliary.context.input, pos_from, pos_to)
        if operator.make_operator then
            return operator.make_operator(inner, positional)
        end
        return logic.make_unary_operator(inner, operator, positional)
    end

    local layer_aux = compute_layer_aux(auxiliary, number)

    local function set_from(when_)
        pos_from = when_
    end
    local context = auxiliary.context
    local expected = context:Label("expected_" .. auxiliary.name)
    -- label the postfix position: "x [..]" is a legal continuation of
    -- every operand, so a missing "[" is still an expectation.  (Same
    -- non-consuming construction as the infix label: a Cmt inside the
    -- ^0 body would make LPeg reject it as possibly-empty.)
    -- each completed "[..]" journals a "modify" operand end — the
    -- operand as a whole is the atom before '[' (svc's
    -- atom_start_before), so `from` is the layer operand's start
    local modify_end = lpeg_util.note(function(p)
        return {kind = "oend", okind = "modify",
                from = pos_from, to = p}
    end)
    local with_op = context:Cp() / set_from * layer_aux.next_layer_var
                  * (layer_aux.precedence_ops * context:Cp() * modify_end
                     % make_unary_operator_postfix)^0
    -- the postfix result (or the plain operand when no op matched) is
    -- the operand any following continuation builds on
    with_op = lpeg.Cg(with_op, "sug_after") * lpeg.Cb("sug_after")
    if auxiliary.postfix_label then
        with_op = with_op * (context:Label(auxiliary.postfix_label)
                             + parsing_context.Suggest(
                                 lpeg.Cb("sug_after") + lpeg.Cc(nil),
                                 operator_suggest_cont(
                                     auxiliary.by_precedence[
                                         layer_aux.precedence]))
                             + lpeg.P(true))
    end
    result[layer_aux.precedence_var_name] = with_op + expected
end

local function handle_custom_layer(result, auxiliary, number)
    local layer_aux = compute_layer_aux(auxiliary, number)

    local with_op = layer_aux.next_layer_var
    local first_var = auxiliary.prececence_vars[auxiliary.all_precedences[1]]
    for _,op in ipairs(auxiliary.by_precedence[layer_aux.precedence]) do
        local parser = auxiliary.operator_parsers[op.name](first_var)
        with_op = with_op + parser
    end
    with_op = with_op + auxiliary.context:Label("expected_" .. auxiliary.name)
    result[layer_aux.precedence_var_name] = with_op
end

local function make_formula_parser(parameters)
    assert(parameters)
    assert(parameters.context)
    local auxiliary = compute_auxiliary(parameters)
    local name = auxiliary.name
    local result = {}
    table.insert(result, lpeg.V(name))
    for number, precedence in ipairs(auxiliary.all_precedences) do
        local sample_op = auxiliary.by_precedence[precedence][1]
        if sample_op.arity == 2 and sample_op.notation == "infix" then
            handle_binary_infix_layer(result, auxiliary, number)
        elseif sample_op.arity == 1 and sample_op.notation == "prefix" then
            handle_unary_prefix_layer(result, auxiliary, number)
        elseif sample_op.arity == 1 and sample_op.notation == "postfix" then
            handle_unary_postfix_layer(result, auxiliary, number)
        else
            handle_custom_layer(result, auxiliary, number)
        end
    end
    handle_last_layer(result, auxiliary)
    result[name] = auxiliary.prececence_vars[auxiliary.all_precedences[1]]
    return result
end

return make_formula_parser
