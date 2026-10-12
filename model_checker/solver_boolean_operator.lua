---
---

local unpack = table.unpack or unpack

local util = require "lib.util"
local binary_semantics = require "model_checker.operators_binary_semantics"
local compare_semantics = require "model_checker.operators_compare_semantics"
local result_display = require "model_checker.result_display"
local varterm = require "logic.varterm"
local bindings = require "model_checker.bindings"
local boolean_claim = require "model_checker.boolean_claim"

local function bool_to_distribution(input)
    if input then
        return {T=1.0, F=0.0}
    else
        return {T=0.0, F=1.0}
    end
end

local solver = {}

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local property = self.parameters.property
    if property:get_type() ~= "operator" then
        return false
    end
    if not binary_semantics[property:get_operator_name()] then
        return false
    end
    local operator = property:get_operator()
    for i = 1, operator.arity do
        local child = property:get_child(i)
        if child:get_type() == "identifier"
           and not (self.parameters.bindings
                    and self.parameters.bindings[child:get_identifier()]) then
            -- a bare identifier is a variable, not a claim — unless it
            -- names a Boolean-domain variable, where it reads as the
            -- claim "X = <truthy outcome>" ("GOAL_2 ∧ RApp1" is
            -- "GOAL_2 = true ∧ RApp1 = true" on andes-style domains)
            local values = self.parameters.model:get_values_or_nil(
                bindings.resolve(self.parameters, child:get_identifier()))
            if not boolean_claim.is_boolean_domain(values) then
                return false
            end
        end
    end
    return true
end

function solver:get_priority()
    return 3
end

function solver:get_name()
    return "boolean_operator"
end

local function make_variable_name(property)
    local as_string = tostring(property)
    local result = {}
    for i=1,#as_string do
        local letter = as_string:byte(i)
        if string.byte("a") <= letter and letter <= string.byte("z")
                or string.byte("A") <= letter and letter <= string.byte("Z")
                or string.byte("0") <= letter and letter <= string.byte("9")
                or string.byte("_") == letter
        then
            table.insert(result, string.char(letter))
        else
            table.insert(result, string.format("x%Xx", letter))
        end
    end
    result = table.concat(result)
    return result
end


local function make_boolean_node(model, property, atoms_list, parameters)
    -- the name carries the position suffix when the subtree embeds a
    -- fresh literal (DIST/PDIST/mixture-MUX): two textually identical
    -- compounds are then distinct variables
    local new_variable_name = make_variable_name(property)
                            .. varterm.fresh_suffix(property)
    local operator = property:get_operator()
    local inner_variables = {}
    for i=1,operator.arity do
        local child = property:get_child(i)
        -- a bare Boolean-domain variable materialises as its
        -- "X = <truthy outcome>" claim atom
        parameters.property = boolean_claim.as_claim(parameters, child)
                              or child
        table.insert(inner_variables, parameters.model_check(parameters))
        parameters.property = property
    end
    -- every operand must denote a Boolean ({F,T}) atom — a LET-bound
    -- identifier may name a non-Boolean variable, which the service
    -- layer rejects and direct evaluation must not silently coerce
    for _, child_var_name in ipairs(inner_variables) do
        local child_values = model:get_values(child_var_name)
        assert(#child_values == 2 and child_values[1] == "F"
               and child_values[2] == "T",
               {key="not_boolean",
                positional=property:get_positional()})
    end
    model:set_values(new_variable_name, {"F", "T"})
    -- operands that resolve to the SAME atom (e.g. the two identical
    -- texts in "MAP(X) ↔ MAP(X)", which mangle to one aux variable)
    -- must share one value per configuration — the parent set is the
    -- deduplicated operand list, so "a ↔ a" ranges over {a=F, a=T} and
    -- evaluates iff(a,a) = true instead of colliding on row[a]
    local parents, seen = {}, {}
    for _, child_var_name in ipairs(inner_variables) do
        if not seen[child_var_name] then
            seen[child_var_name] = true
            parents[#parents + 1] = child_var_name
        end
    end
    local num_values = 2^#parents
    for value_number = 0,num_values-1 do
        local remaining = value_number
        local row = {}
        for parent_number = 1,#parents do
            local parent_name = parents[parent_number]
            local parent_values = model:get_values(parent_name)
            local parent_value = remaining % 2
            row[parent_name] = parent_values[parent_value + 1]
            remaining = math.floor(remaining / 2)
        end
        local child_boolean_values = {}
        for child_number = 1,operator.arity do
            table.insert(child_boolean_values,
                         row[inner_variables[child_number]] == "T")
        end
        local op_result = binary_semantics[property:get_operator_name()](unpack(child_boolean_values))
        local op_distr = bool_to_distribution(op_result)
        model:set_probabilies(new_variable_name, row, op_distr)
    end
    table.insert(atoms_list, new_variable_name)
    result_display.compose(parameters, new_variable_name, property, inner_variables)
    return new_variable_name
end

function solver:check()
    local parameters = self.parameters
    return make_boolean_node(parameters.model, parameters.property, parameters.atoms_list, parameters)
end

return solver
