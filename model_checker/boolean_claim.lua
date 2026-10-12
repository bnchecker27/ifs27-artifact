---
--- A bare identifier in a Boolean position (claim operand of a logical
--- connective, evidence of P/MAP/MPE, a conditional's condition) denotes
--- the claim "X = <truthy outcome>" when X's domain is Boolean-spelled.
--- The domain predicate lives in lib/util (util.true_outcome) so the
--- service-side validator shares it; this module only holds the solver
--- half: rewriting the bare identifier into the equivalent comparison
--- node, so every solver consumes one mechanism.
---

local util = require "lib.util"
local logic = require "logic.logic"
local operators = require "logic.operators"
local bindings = require "model_checker.bindings"

local boolean_claim = {}

local equal_operator = operators.make_name_to_operator_map(
    operators.compare_operators)["equal"]

boolean_claim.true_outcome = util.true_outcome
boolean_claim.is_boolean_domain = util.is_boolean_domain

-- the "X = <truthy outcome>" comparison node a bare Boolean-domain
-- identifier denotes in claim position, or nil when node is not a bare
-- Boolean-domain identifier.  A LET-bound name denoting an {F,T} atom
-- needs no wrapper — it already IS a claim atom.  The comparison keeps
-- the identifier's position so errors point at the user's text.
function boolean_claim.as_claim(parameters, node)
    if type(node) ~= "table" or node:get_type() ~= "identifier" then
        return nil
    end
    local raw = node:get_identifier()
    local values = parameters.model:get_values_or_nil(
        bindings.resolve(parameters, raw))
    local true_outcome = util.true_outcome(values)
    if not true_outcome then
        return nil
    end
    if parameters.bindings and parameters.bindings[raw]
       and values[1] == "F" and values[2] == "T" then
        return nil
    end
    local positional = node:get_positional()
    local rhs = logic.make_identifier(true_outcome, positional)
    return logic.make_binary_operator(node, rhs, equal_operator, positional)
end

return boolean_claim
