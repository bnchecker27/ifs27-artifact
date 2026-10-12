---
---

local util = require "lib.util"
local sampler_random = require "model_checker.sampler_random"
local sampler_enumerate = require "model_checker.sampler_enumerate"

local function compute_num_assignments(model)
    local variable_order = model:get_variables()
    local num_assignments = 1
    for _,variable in ipairs(variable_order) do
        local values = model:get_values(variable)
        num_assignments = num_assignments * #values
    end
    return num_assignments
end

local function make_sampler_auto(model, options)
    if options.sampler == "enumerate" then
        return sampler_enumerate(model, options)
    elseif options.sampler == "random" then
        return sampler_random(model, options)
    elseif options.sampler == "auto" or not options.sampler then
        local num_samples = options:get("num_samples")
        local num_assignments = compute_num_assignments(model)
        if num_assignments <= num_samples then
            return sampler_enumerate(model, options)
        else
            return sampler_random(model, options)
        end
    end
end

return make_sampler_auto
