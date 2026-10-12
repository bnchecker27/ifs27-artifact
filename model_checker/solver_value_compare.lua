---
---

local util = require "lib.util"
local compare_semantics = require "model_checker.operators_compare_semantics"
local result_display = require "model_checker.result_display"
local varterm = require "logic.varterm"

local solver = {}

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local parameters = self.parameters
    local property = parameters.property
    if property:get_type() ~= "operator" then
        return false
    end
    if not compare_semantics[property:get_operator_name()] then
        return false
    end
    if property:get_child(1):get_type() == "identifier" then
        return false
    end
    if property:get_child(2):get_type() == "identifier" then
        return false
    end
    -- a variable-valued operand (DIST/RENAME/MUX/FAMILY literal,
    -- numexpr, conditioned variable) belongs to the domain-aware
    -- compare solvers: here model_check would yield the operand's aux
    -- variable NAME, so "DIST(…) = DIST(…)" would compare two strings
    -- and always come out false
    if varterm.is_variable_term(property:get_child(1))
       or varterm.is_variable_term(property:get_child(2)) then
        return false
    end
    return true
end

function solver:get_priority()
    return 3
end

function solver:get_name()
    return "value_compare"
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

local function bool_to_distribution(input)
    if input then
        return {T=1.0, F=0.0}
    else
        return {T=0.0, F=1.0}
    end
end

function solver:check()
    local parameters = self.parameters
    local property = parameters.property
    local model = parameters.model
    local op_name = property:get_operator_name()
    local new_variable_name = make_variable_name(property)

    model:set_values(new_variable_name, {"F", "T"})
    -- Use a uniform placeholder while evaluating the sub-properties.  The
    -- variable is not yet part of the query/evidence, so any proper
    -- distribution is neutral once summed out.  Without this the factor for
    -- the new variable is all zero, which poisons products in inner solvers.
    model:set_probabilies(new_variable_name, {}, {F = 0.5, T = 0.5})

    parameters.property = property:get_child(1)
    local left = parameters.model_check(parameters)
    parameters.property = property:get_child(2)
    local right = parameters.model_check(parameters)
    parameters.property = property

    local bool_value = compare_semantics[op_name](left, right)
    model:set_probabilies(new_variable_name, {}, bool_to_distribution(bool_value))
    table.insert(parameters.atoms_list, new_variable_name)
    result_display.comparison(parameters, new_variable_name, property)
    return new_variable_name
end

return solver
