---
--- Solver for arithmetic operators on numeric values
---

local unpack = table.unpack or unpack

local arithmetic_semantics = {
    ["plus"] = function(op1, op2)
        return op1 + op2
    end,
    ["minus"] = function(op1, op2)
        return op1 - op2
    end,
    ["times"] = function(op1, op2)
        return op1 * op2
    end,
    ["divide"] = function(op1, op2)
        if op2 == 0 then
            error({key="division_by_zero"})
        end
        return op1 / op2
    end
}

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
    return arithmetic_semantics[property:get_operator_name()] ~= nil
end

function solver:get_priority()
    return 2
end

function solver:get_name()
    return "arithmetic_operator"
end

function solver:check()
    local parameters = self.parameters
    local model_check = parameters.model_check
    local property = parameters.property
    local operator = property:get_operator()
    local results = {}
    for i = 1, operator.arity do
        parameters.property = property:get_child(i)
        table.insert(results, model_check(parameters))
        parameters.property = property
    end
    return arithmetic_semantics[property:get_operator_name()](unpack(results))
end

return solver
