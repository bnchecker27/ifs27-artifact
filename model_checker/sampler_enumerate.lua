---
---

local static_bn = require "model_checker.static_bn"
local toposort = require "model_checker.toposort"

local function make_sampler_enumerate(model)
    local result = {}
--    local variables = toposort(model)
    result.enum_model = static_bn(model, variables)
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
        for i=0,enum_model:get_num_assignments()-1 do
            enum_model:set_assignment_number_to_assignment(assignment,i)
            local prob = 1.0
            for var=0,enum_model:get_num_variables()-1 do
                local var_prob = enum_model:compute_assignment_variable_prob(assignment, var)
                prob = prob * var_prob
            end
            callback(assignment, prob)
        end
    end

    return result
end

return make_sampler_enumerate
