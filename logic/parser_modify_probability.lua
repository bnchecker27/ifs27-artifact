---
---
---
local lpeg = require "lpeg"
local lpeg_util = require "lib.lpeg_util"
local logic = require "logic.logic"
local make_positional = require "lib.positional"

local Space = lpeg_util.Space

-- Create a binary '='/'↦' operator for an intervention clause.
-- The operator is named "equal" so the explainer and tostring logic
-- already know how to render it, but its default symbol is the actual
-- arrow that appeared in the input.
local function create_eq_op(symbol)
    return {
        is_operator = true,
        name = "equal",
        default_symbol = symbol,
        arity = 2,
        precedence = 6,
        notation = "infix",
        associativity = "none",
        associative = false,
    }
end

local function make_parser(context)
    -- Build an identifier AST from the captured positions.
    -- 'from' is the position before the first non-space character of the
    -- identifier; 'to' is the position after the identifier and its
    -- trailing space.  make_positional strips surrounding spaces.
    local function make_identifier(from, name, to)
        local positional = make_positional(context.input, from, to - 1)
        return logic.make_identifier(name, positional)
    end

    -- Build a numeric value AST from the captured positions.
    local function make_value(from, value, to)
        local positional = make_positional(context.input, from, to - 1)
        return logic.make_value(value, positional)
    end

    local function compute_symbol_string(self)
        local result = {}
        table.insert(result, "[")
        table.insert(result, tostring(self.identifier))
        table.insert(result, ":")
        for k,v in pairs(self.prob_map) do
            table.insert(result, tostring(k))
            table.insert(result, "=")
            table.insert(result, tostring(v))
            table.insert(result, ",")
        end
        result[#result] = nil
        if self.condition then
            table.insert(result, "|")
            for k,v in pairs(self.condition) do
                table.insert(result, tostring(k))
                table.insert(result, "=")
                table.insert(result, tostring(v))
                table.insert(result, ",")
            end
            result[#result] = nil
        end
        table.insert(result, "]")
        result = table.concat(result)
        return result
    end

    -- Common operator builder: creates the modify_probability AST with the
    -- inner formula plus the intervention clauses as real subformulae.
    local function make_modify_operator(target_ast, prob_map_asts, condition_asts)
        local op = {
            is_operator = true,
            name = "modify_probability",
            precedence = 7,
            notation = "postfix",
            compute_symbol_string = compute_symbol_string,
            identifier = target_ast:get_identifier(),
            target_ast = target_ast,
            prob_map = {},
            condition = {},
        }

        -- Maintain the maps expected by the model checker/validator.
        -- A □ placeholder leaf has no identifier/value payload for the
        -- maps — validation flags the entry as incomplete anyway.
        for _, map_ast in ipairs(prob_map_asts) do
            local left = map_ast:get_child(1)
            local right = map_ast:get_child(2)
            if left.get_identifier and right.get_value then
                op.prob_map[left:get_identifier()] = right:get_value()
            end
        end
        for _, cond_ast in ipairs(condition_asts) do
            local left = cond_ast:get_child(1)
            local right = cond_ast:get_child(2)
            if left.get_identifier and right.get_identifier then
                op.condition[left:get_identifier()] = right:get_identifier()
            end
        end

        -- Custom constructor invoked by parser_formula after the inner
        -- formula has been parsed.  It assembles the final list of children
        -- and updates the operator arity to match.
        function op.make_operator(inner, positional)
            local children = {inner, target_ast}
            for _, c in ipairs(prob_map_asts) do
                table.insert(children, c)
            end
            for _, c in ipairs(condition_asts) do
                table.insert(children, c)
            end
            op.arity = #children
            op.prob_map_count = #prob_map_asts
            op.condition_count = #condition_asts
            return logic.make_operator(children, op, positional)
        end

        -- tostring just returns the original source text for this bracket.
        function op.tostring(what)
            local pos = what:get_positional()
            if pos and pos.text then
                return pos.text
            end
            return "[...]"
        end

        return op
    end

    -- Parser pieces ---------------------------------------------------------

    -- The box placeholder (□ or \box) is accepted wherever the bracket
    -- expects an identifier or a number — target, outcome, probability,
    -- condition variable/value — so a partially built intervention stays
    -- parseable while a slot is unfilled; semantic validation flags it
    -- as incomplete.
    local BoxLit = lpeg.P("\226\150\161") + (lpeg.P("\\") * lpeg.P("box"))

    local function make_box_leaf(from, _, to)
        local positional = make_positional(context.input, from, to - 1)
        return logic.make_box(positional)
    end

    local IdentifierParser = context:Cp() * lpeg_util.Identifier * context:Cp() / make_identifier
    local RealParser = context:Cp() * (lpeg_util.Real / tonumber) * context:Cp() / make_value
    local BoxParser = context:Cp() * (lpeg.C(BoxLit) * Space) * context:Cp() / make_box_leaf

    local IdentifierOrError = lpeg_util.labeled(IdentifierParser + BoxParser,
                                                "expected_identifier")
    local RealOrError = lpeg_util.labeled(RealParser + BoxParser,
                                          "expected_number")

    -- suggestion annotations: a failed slot reports what could go there —
    -- target/condition variables accept model variables, outcome slots
    -- accept the governing variable's outcomes, prob slots a number.
    -- The governing variable's node is routed to the slot through a named
    -- group capture ("br_target" / "cond_lhs"), re-emitted with Cb so the
    -- regular capture stream is unchanged.
    local function outcome_of(node)
        if type(node) == "table" and type(node.get_identifier) == "function" then
            local ok, name = pcall(function() return node:get_identifier() end)
            if ok and type(name) == "string" then
                return {kind = "outcome-of", var = name}
            end
        end
        return {kind = "ident"}
    end
    -- the bracket slots: brole tells the resolver which candidates a
    -- slot takes (target/condition variables, outcome names, probs)
    -- each bracket slot's operand journals an "atom" note so the
    -- operand-tail walk can classify the last-completed slot
    local VarOrError = lpeg_util.suggestable(
        lpeg_util.marked(IdentifierOrError, "atom"), {kind = "variable"})
    local OutcomeOfTarget = lpeg_util.suggestable_cb(
        lpeg_util.marked(IdentifierOrError, "atom"), "br_target", outcome_of)
    local OutcomeOfCond = lpeg_util.suggestable_cb(
        lpeg_util.marked(IdentifierOrError, "atom"), "cond_lhs", outcome_of)
    local ProbOrError = lpeg_util.suggestable(
        lpeg_util.marked(RealOrError, "atom"), {kind = "prob"})
    local function TargetOrError(p)  -- target var + store it for the slots
        return lpeg.Cg(
            lpeg_util.sug_scope(p, {brole = "target", slot = "any"}),
            "br_target") * lpeg.Cb("br_target")
    end

    local LBrack = lpeg_util.LBrack
    local RBrackOrError = lpeg_util.labeled(lpeg_util.RBrack, "expected_rbrack", {kw="]"})
    local ColonOrError = lpeg_util.labeled(
        lpeg_util.sep_note_silent(lpeg.P":", "colon",
                                  {nslot = "compare"}) * Space,
        "expected_colon", {kw=":"})
    local BarOrError = lpeg_util.labeled(
        lpeg_util.sep_note_silent(lpeg.P"|", "sep",
                                  {nslot = "any"}) * Space,
        "expected_bar", {kw="|"})

    -- Capture the actual arrow symbol (=, ->, or ↦) and consume trailing space.
    -- Journals as a compare-class separator so the resolver's
    -- compare_tail finds the "outcome op value" boundary.
    local MapsToPattern = lpeg_util.string_array_S{"=", "->", "↦"}
    local MapsToSymbol = (lpeg_util.labeled(
        lpeg_util.sep_note(lpeg.C(MapsToPattern), "csep",
            function(_, sym)
                return {cls = "cmp", sym = sym,
                        nslot = sym == "↦" and "other" or "compare"}
            end),
        "expected_maps_to", {kw="↦"})) * Space

    local ProbMapEntry = context:Cp()
                       * lpeg_util.sug_scope_src(OutcomeOfTarget,
                           "br_target", {brole = "mapkey"}, "btarget")
                       * context:Cp()
                       * MapsToSymbol
                       * context:Cp()
                       * lpeg_util.sug_scope_src(ProbOrError,
                           "br_target", {brole = "mapval"}, "btarget")
                       * context:Cp()
                       / function(left_from, left_ast, left_to, arrow, right_from, right_ast, right_to)
                           local op = create_eq_op(arrow)
                           local positional = make_positional(context.input, left_from, right_to - 1)
                           return logic.make_binary_operator(left_ast, right_ast, op, positional)
                         end
    local ProbMap = lpeg_util.make_list_parser(ProbMapEntry)

    local ConditionEntry = context:Cp()
                         * lpeg.Cg(lpeg_util.sug_scope(VarOrError,
                                                     {brole = "condvar"}),
                                   "cond_lhs") * lpeg.Cb("cond_lhs")
                         * context:Cp()
                         * MapsToSymbol
                         * context:Cp()
                         * lpeg_util.sug_scope(OutcomeOfCond,
                                               {brole = "condval"})
                         * context:Cp()
                         / function(left_from, left_ast, left_to, arrow, right_from, right_ast, right_to)
                             local op = create_eq_op(arrow)
                             local positional = make_positional(context.input, left_from, right_to - 1)
                             return logic.make_binary_operator(left_ast, right_ast, op, positional)
                           end
    local Condition = lpeg_util.make_list_parser(ConditionEntry)

    local RBrackOrBar = lpeg_util.labeled(
        lpeg_util.RBrack + lpeg_util.Bar * Condition * RBrackOrError,
        "expected_rbrack_or_bar",
        {kind = "ops", symbols = {"]", "|"}})

    -- Form 1: [target: value=prob, ... [| cond=val, ...]]
    local ColonForm = context:Cp() * LBrack
                    * context:Cp() * TargetOrError(VarOrError) * context:Cp()
                    * ColonOrError
                    * ProbMap
                    * RBrackOrBar
                    * context:Cp()
                    / function(pos_from, target_from, target_ast, target_to, prob_map_asts, condition_param, pos_to)
                        if type(condition_param) == "number" and pos_to == nil then
                            pos_to = condition_param
                            condition_param = {}
                        end
                        return make_modify_operator(target_ast, prob_map_asts or {}, condition_param or {})
                      end

    -- Form 2 (paper with condition): [target = value | cond=val ... ↦ prob]
    local PaperFormCond = context:Cp() * LBrack
                        * context:Cp() * TargetOrError(VarOrError) * context:Cp()
                        * MapsToSymbol
                        * context:Cp() * lpeg_util.sug_scope_src(OutcomeOfTarget,
                            "br_target", {brole = "mapval"}, "btarget") * context:Cp()
                        * BarOrError
                        * Condition
                        * context:Cp() * MapsToSymbol
                        * context:Cp() * lpeg_util.sug_scope_src(ProbOrError,
                            "br_target", {brole = "mapval"}, "btarget") * context:Cp()
                        * RBrackOrError
                        * context:Cp()
                        / function(pos_from, target_from, target_ast, target_to,
                                   arrow1, value_from, value_ast, value_to,
                                   condition_asts, arrow_from, arrow2, prob_from, prob_ast, prob_to)
                            local map_positional = make_positional(context.input, arrow_from, prob_to - 1)
                            local map_op = create_eq_op(arrow2)
                            local map_ast = logic.make_binary_operator(value_ast, prob_ast, map_op, map_positional)
                            return make_modify_operator(target_ast, {map_ast}, condition_asts)
                          end

    -- Form 3 (paper without condition): [target = value ↦ prob]
    local PaperFormNoCond = context:Cp() * LBrack
                          * context:Cp() * TargetOrError(VarOrError) * context:Cp()
                          * MapsToSymbol
                          * context:Cp() * lpeg_util.sug_scope_src(OutcomeOfTarget,
                              "br_target", {brole = "mapval"}, "btarget") * context:Cp()
                          * context:Cp() * MapsToSymbol
                          * context:Cp() * lpeg_util.sug_scope_src(ProbOrError,
                              "br_target", {brole = "mapval"}, "btarget") * context:Cp()
                          * RBrackOrError
                          * context:Cp()
                          / function(pos_from, target_from, target_ast, target_to,
                                     arrow1, value_from, value_ast, value_to,
                                     arrow_from, arrow2, prob_from, prob_ast, prob_to)
                              local map_positional = make_positional(context.input, arrow_from, prob_to - 1)
                              local map_op = create_eq_op(arrow2)
                              local map_ast = logic.make_binary_operator(value_ast, prob_ast, map_op, map_positional)
                              return make_modify_operator(target_ast, {map_ast}, {})
                            end

    local parser = ColonForm + PaperFormCond + PaperFormNoCond

    return parser
end

return make_parser
