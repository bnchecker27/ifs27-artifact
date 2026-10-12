---
---

local util = require "lib.util"
local parser_bif = require "bayesian_network.parser_bif"
local parser_formula = require "logic/parser_bn_logic"
local model_checker = require "model_checker.model_checker"
local options_manager = require "lib.options_manager"

local success, result = pcall(function()
    local options = options_manager.parse_command_line(arg)

    if options:is_set("seed") then
        math.randomseed(options:get("seed"))
    end

    local input = util.read_from_file(options:get("model"))
    if not input then
        error({key="file_read_error", parameters={path=options:get("model")}})
    end
    local formula = parser_formula(options:get("property"),
                                   options:get("features"))
    local bn = parser_bif(input, options)
    return model_checker(bn, formula, options)
end)

if not success then
    print(util.translate_error(result))
    print(options_manager:compute_command_line_string())
    os.exit(1)
end

-- Format result based on type
if type(result) == "boolean" then
    print("Result: " .. (result and "true" or "false"))
elseif type(result) == "number" then
    print("Probability: " .. result)
elseif type(result) == "table" then
    print("Result:")
    local mt = getmetatable(result)
    if mt and mt.__order then
        for _, key in ipairs(mt.__order) do
            print("  " .. key .. " = " .. result[key])
        end
    else
        for key, value in pairs(result) do
            print("  " .. key .. " = " .. value)
        end
    end
else
    print(result)
end
