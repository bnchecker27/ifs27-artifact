---
---

local ffi = require "ffi"

local function compute_num_variables(model, variable_order)
    return #variable_order
end

local function compute_number_to_variable(model, variable_order)
    local result = {}
    for number,variable in ipairs(variable_order) do
        result[number - 1] = variable
    end
    return result
end

local function compute_variable_to_number(model, variable_order)
    local variable_to_number = {}
    for variable_number,variable in ipairs(variable_order) do
        variable_to_number[variable] = variable_number - 1
    end
    return variable_to_number
end

local function compute_num_assignments(model, variable_order)
    local num_assignments = 1
    for _,variable in ipairs(variable_order) do
        local values = model:get_values(variable)
        num_assignments = num_assignments * #values
    end
--    assert(num_assignments < 2^32 - 1, num_assignments)
    return num_assignments
end

local function compute_num_values_of_variables(model, variable_order)
    local num_values_of_variable = ffi.new("int[?]", #variable_order)
    for variable_number=0,#variable_order-1 do
        local variable = variable_order[variable_number+1]
        num_values_of_variable[variable_number] = #model:get_values(variable)
    end
    return num_values_of_variable
end

local function compute_variable_probs_start(model, variable_order)
    local result = ffi.new("int[?]", #variable_order+1)
    local size = 0
    result[0] = 0
    for variable_number,variable in ipairs(variable_order) do
        local variable_size = 1;
        for _,dependent in ipairs(model:get_dependents(variable)) do
            local num_dependent_values = #model:get_values(dependent)
            variable_size = variable_size * num_dependent_values
        end
        local num_values = #model:get_values(variable)
        variable_size = variable_size * num_values
        size = size + variable_size
        result[variable_number] = size
    end
    return result
end

local function compute_dep_idx_from_to(model, variable_order)
    local result = ffi.new("int[?]", #variable_order + 1)
    result[0] = 0
    local index = 0
    for variable_number,variable in ipairs(variable_order) do
        index = index + #model:get_dependents(variable) + 1
        result[variable_number] = index
    end
    return result
end

local function compute_dep_index(model, variable_to_number, variable_order)
    local size = 0
    for _,variable in ipairs(variable_order) do
        size = size + #model:get_dependents(variable) + 1
    end
    local result = ffi.new("int[?]", size + 1)
    local index = 0
    for variable_number,variable in ipairs(variable_order) do
        result[index] = variable_number - 1
        index = index + 1
        for _,dependent in ipairs(model:get_dependents(variable)) do
            local dependent_number = variable_to_number[dependent]
            result[index] = dependent_number
            index = index + 1
        end
    end
    return result
end

local function compute_cdp_size(model, variable)
    local cdp_size = 1;
    for _,dependent in ipairs(model:get_dependents(variable)) do
        local num_dependent_values = #model:get_values(dependent)
        cdp_size = cdp_size * num_dependent_values
    end
    local num_values = #model:get_values(variable)
    cdp_size = cdp_size * num_values
    return cdp_size
end


local function compute_probabilities_size(model, variable_order)
    local size = 0
    for _,variable in ipairs(variable_order) do
        size = size + compute_cdp_size(model, variable)
    end
    return size
end

local function compute_probabilities(model, variable_order)
    local size = compute_probabilities_size(model, variable_order)
    local result = ffi.new("double[?]", size)
    local variables = variable_order
    local index = 0
    for _,variable in ipairs(variables) do
        local cdp_size = compute_cdp_size(model, variable)
        local row = {}
        for cdp_value_number = 0,cdp_size - 1 do
            local rest = cdp_value_number
            local value_number = math.floor(rest % #model:get_values(variable))
            rest = math.floor(rest / #model:get_values(variable))
            for _,dependent in ipairs(model:get_dependents(variable)) do
                local num_dependent_values = #model:get_values(dependent)
                local dependent_value_number = math.floor(rest % num_dependent_values)
                local dependent_value = model:get_values(dependent)[dependent_value_number + 1]
                row[dependent] = dependent_value
                rest = math.floor(rest / num_dependent_values)
            end
            local probabilities = model:get_probabilities(variable, row)
            local value = model:get_values(variable)[value_number + 1]
            local probability = probabilities[value]
            result[index] = probability
            index = index + 1
        end
    end
    return result
end

local function build_static_model(model, variable_order)
    assert(model)
    if not variable_order then
        variable_order = model:get_variables()
    end
    local result = {}
    result.num_variables = compute_num_variables(model, variable_order)
    result.number_to_variable = compute_number_to_variable(model, variable_order)
    result.variable_to_number = compute_variable_to_number(model, variable_order)
    result.num_assignments = compute_num_assignments(model, variable_order)
    result.num_values_of_variable = compute_num_values_of_variables(model, variable_order)
    result.variable_probs_start = compute_variable_probs_start(model, variable_order)
    result.dep_idx_from_to = compute_dep_idx_from_to(model, variable_order)
    result.dep_index = compute_dep_index(model, result.variable_to_number, variable_order)
    result.probabilities = compute_probabilities(model, variable_order)

    function result:get_variable_to_number(variable)
        return self.variable_to_number[variable]
    end
    function result:get_number_to_variable(number)
        return self.number_to_variable[number]
    end
    function result:get_num_assignments()
        return self.num_assignments
    end
    function result:get_num_variables()
        return self.num_variables
    end
    function result:set_assignment_number_to_assignment(assignment, number)
        for variable_number=0,self:get_num_variables()-1 do
            local num_values = self.num_values_of_variable[variable_number]
            assignment[variable_number] = math.floor(number % num_values)
            number = math.floor(number / num_values)
        end
    end
    function result:new_assignment()
        return ffi.new("int[?]", self.num_variables)
    end
    function result:compute_assignment_variable_prob(assignment, variable_number)
        local index = self.variable_probs_start[variable_number]
        local multiplier = 1
        for var_index = self.dep_idx_from_to[variable_number],self.dep_idx_from_to[variable_number+1]-1 do
            local dependency = self.dep_index[var_index]
            local dependency_num_values = self.num_values_of_variable[dependency]
            local dependency_value = assignment[dependency]
            index = index + dependency_value * multiplier
            multiplier = multiplier * dependency_num_values
        end
        local prob = self.probabilities[index]
        return prob
    end

    return result
end

return build_static_model
