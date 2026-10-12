---
---

local dependence = require "model_checker.dependence"
local util = require "lib.util"
local bindings = require "model_checker.bindings"

local solver = {}

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

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local parameters = self.parameters
    local property = parameters.property
    return property:get_type() == "operator" and property:get_operator_name() == "idp"
end

function solver:get_priority()
    return 1
end

function solver:get_name()
    return "idp"
end

function solver:check()
    local parameters = self.parameters
    local property = parameters.property
    local model = parameters.model
    local operator = property:get_operator()
    local left = bindings.resolve(parameters, operator.left)
    local right = bindings.resolve(parameters, operator.right)
    local cond = {}
    for i, cond_var in ipairs(operator.cond) do
        cond_var = bindings.resolve(parameters, cond_var)
        assert(model:is_variable(cond_var),
                {key="idp_cond_not_variable",
                 parameters={variable=cond_var},
                 positional=property:get_positional()})
        cond[i] = cond_var
    end
    assert(model:is_variable(left),
            {key="idp_left_not_variable",
             parameters={variable=left},
             positional=property:get_positional()})
    assert(model:is_variable(right),
            {key="idp_right_not_variable",
             parameters={variable=right},
             positional=property:get_positional()})
    local given = util.list_to_set(cond)
    local reachable = dependence(model, left, given)
    local result = not util.toboolean(reachable[right])

    local new_variable_name = make_variable_name(property)
    model:set_values(new_variable_name, {"F", "T"})
    model:set_probabilies(new_variable_name, {}, bool_to_distribution(result))
    table.insert(parameters.atoms_list, new_variable_name)
    return new_variable_name
end

return solver
