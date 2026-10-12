---
---

local options = {
    help = {
        command_line_required = false,
        description_key = "help",
        value_type = "boolean"
    },
    model = {
        command_line_required = true,
        description_key = "model",
        value_type = "string"
    },
    property = {
        command_line_required = true,
        description_key = "property",
        value_type = "string"
    },
    num_samples = {
        command_line_required = false,
        default = 100000,
        description_key = "num_samples",
        value_type = "number",
        parse = function(value)
            local util = require "lib.util"
            return util.validate_numeric_parameter(value, "num_samples", nil, false)
        end
    },
    solvers = {
        command_line_required = false,
        description_key = "solvers",
        value_type = "string"
    },
    disable_solvers = {
        command_line_required = false,
        description_key = "disable_solvers",
        value_type = "string"
    },
    enable_solvers = {
        command_line_required = false,
        description_key = "enable_solvers",
        value_type = "string"
    },
    probability_tolerance = {
        command_line_required = false,
        default = 1.0E-6,
        description_key = "probability_tolerance",
        value_type = "number",
        parse = function(value)
            local util = require "lib.util"
            return util.validate_numeric_parameter(value, "probability_tolerance", nil, false)
        end
    },
    seed = {
        command_line_required = false,
        description_key = "seed",
        value_type = "number",
        parse = function(value)
            local util = require "lib.util"
            return util.validate_numeric_parameter(value, "seed", nil, false)
        end
    },
    -- comma separated optional features ("cond,marginal,chart") or "all";
    -- parsed into a set via lib.features wherever it is consulted
    features = {
        command_line_required = false,
        description_key = "features",
        value_type = "string"
    }
}

return options
