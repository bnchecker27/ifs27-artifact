---
---

local util = require "lib.util"
local static_bn = require "model_checker.static_bn"
local toposort = require "model_checker.toposort"

local function prepare_probabilities_for_sampling(model)
    for variable_number=0,model:get_num_variables()-1 do
        local variable_start = model.variable_probs_start[variable_number]
        local variable_end = model.variable_probs_start[variable_number+1]
        local num_values = model.num_values_of_variable[variable_number]
        local num_entries = (variable_end - variable_start) / num_values
        local index = variable_start
        for _=0,num_entries-1 do
            local sum = 0
            for _=0,num_values-1 do
                local probability = model.probabilities[index]
                model.probabilities[index] = model.probabilities[index] + sum
                sum = sum + probability
                index = index + 1
            end
        end
    end
end

local function make_sampler_random(model, options)
    local result = {}
    local order = toposort(model)
    result.enum_model = static_bn(model, order)
    prepare_probabilities_for_sampling(result.enum_model)

    function result:get_variable_to_number(variable)
        return self.enum_model:get_variable_to_number(variable)
    end
    function result:set_callback(callback)
        self.callback = callback
    end
    function result:run()
        local enum_model = self.enum_model
        local callback = self.callback
        local assignment = enum_model:new_assignment()
        local num_variables = enum_model:get_num_variables()
        local variables_prob_start = enum_model.variable_probs_start
        local num_values_of_variable = enum_model.num_values_of_variable
        local dep_idx_from_to = enum_model.dep_idx_from_to
        local dep_index = enum_model.dep_index
        local probabilities = enum_model.probabilities
        local random = math.random
        local num_samples = options:get("num_samples")
        for _=0,num_samples do
            local dead = false
            for variable = 0,num_variables-1 do
                local current_num_variable_values = num_values_of_variable[variable]
                local index = variables_prob_start[variable]
                local multiplier = current_num_variable_values
                local var_index_from = dep_idx_from_to[variable]+1
                local var_index_to = dep_idx_from_to[variable+1]-1
                for var_index = var_index_from,var_index_to do
                    local dependency = dep_index[var_index]
                    local dependency_num_values = num_values_of_variable[dependency]
                    local dependency_value = assignment[dependency]
                    index = index + dependency_value * multiplier
                    multiplier = multiplier * dependency_num_values
                end
                -- an all-zero CPT row marks a dead world (conditional
                -- operator semantics): its last cumulative entry stays
                -- 0 — reject the sample instead of counting a value
                if probabilities[index + current_num_variable_values - 1] == 0 then
                    dead = true
                    break
                end
                local value = 0
                local prob = random()
                for value_number = 0,current_num_variable_values-1-1 do
                    value = value + (prob > probabilities[index + value_number] and 1 or 0)
                end
                assignment[variable] = value
            end
            if not dead then
                callback(assignment, 1)
            end
        end
    end

    return result
end

return make_sampler_random
