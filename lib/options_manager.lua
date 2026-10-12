local program_options = require "lib.program_options"

local options_manager = {}

function options_manager.make_options()
    local result = {}
    result.settings = {}
    result.options_set = {}
    function result:set(key, value)
        if not program_options[key] then
            error({key="invalid_option", parameters={option=key}})
        end
        if program_options[key].parse then
            value = program_options[key].parse(value)
        end
        self.settings[key] = value
        self.options_set[key] = true
    end
    function result:get(key)
        assert(key)
        if self.options_set[key] then
            return self.settings[key]
        elseif not program_options[key] then
            return nil
        else
            return program_options[key].default
        end
    end
    function result:is_set(key)
        return self.options_set[key]
    end
    return result
end

function options_manager.make_options_init(init)
    local result = options_manager.make_options()
    for key, value in pairs(init) do
        result:set(key, value)
    end
    return result
end


function options_manager.validate_options(options)
    for key,value in pairs(program_options) do
        if value.command_line_required and not options:is_set(key) then
            error({key="missing_parameter", parameters={parameter=key}})
        end
    end
end

local function parse_option(key, value, result)
    result:set(key, value)
end

function options_manager.parse_command_line(arg)
    local result = options_manager.make_options()
    local i = 1
    while i <= #arg do
        if not (arg[i]:sub(1,2) == "--") then
            error({key="invalid_command_format"})
        end
        local key = arg[i]:sub(3, #arg[i])
        
        -- Handle boolean options (like --help)
        if program_options[key] and program_options[key].value_type == "boolean" then
            -- Check if next argument is a value or another option
            if i + 1 <= #arg and not (arg[i + 1]:sub(1,2) == "--") then
                local value = arg[i + 1]
                if value == "true" or value == "false" then
                    result:set(key, value == "true")
                    i = i + 2
                else
                    -- If it's not true/false, assume flag is true and treat next as new option
                    result:set(key, true)
                    i = i + 1
                end
            else
                -- No value provided, assume true
                result:set(key, true)
                i = i + 1
            end
        else
            -- Regular options require a value
            if i + 1 > #arg then
                error({key="invalid_command_format"})
            end
            if arg[i + 1]:sub(1,2) == "--" then
                error({key="invalid_command_format"})
            end
            parse_option(key, arg[i + 1], result)
            i = i + 2
        end
    end
    
    -- If help is requested, show usage and exit
    if result:is_set("help") and result:get("help") then
        print(options_manager.compute_command_line_string())
        os.exit(0)
    end
    
    options_manager.validate_options(result)
    return result
end


function options_manager:compute_command_line_string()
    local locales = require "locales.options_description"
    local lang = locales.en
    local lines = {}
    local max_left_width = 0
    
    -- First pass: calculate max width for alignment
    for key, opt in pairs(program_options) do
        local left_part = "      --" .. key
        if opt.value_type and opt.value_type ~= "boolean" then
            left_part = left_part .. " " .. opt.value_type
        end
        if #left_part > max_left_width then
            max_left_width = #left_part
        end
    end
    
    max_left_width = max_left_width + 2  -- Add padding
    
    -- Second pass: build formatted lines
    for key, opt in pairs(program_options) do
        local left_part = "      --" .. key
        if opt.value_type and opt.value_type ~= "boolean" then
            left_part = left_part .. " " .. opt.value_type
        end
        
        local description = lang[key] or ""
        if opt.default ~= nil then
            description = description .. " (default " .. tostring(opt.default) .. ")"
        end
        
        -- Pad to align descriptions
        local padding = max_left_width - #left_part
        if padding < 2 then
            padding = 2
        end
        
        local line = left_part .. string.rep(" ", padding) .. description
        table.insert(lines, line)
    end
    
    table.sort(lines)
    return "Usage:\n" .. table.concat(lines, "\n")
end

return options_manager
