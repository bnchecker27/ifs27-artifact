---
---

local solver = {}

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local parameters = self.parameters
    local property = parameters.property
    return property:get_type() == "value"
end

function solver:get_priority()
    return 1
end

function solver:get_name()
    return "value"
end

function solver:check()
    local parameters = self.parameters
    local property = parameters.property
    return property:get_value()
end

return solver
