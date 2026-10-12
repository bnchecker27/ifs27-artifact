---
---

local lpeg = require "lpeg"
local logic = require "logic.logic"
local make_positional = require "lib.positional"
local constant = require "logic.constant"

local Space = lpeg.S(" \n\t")^0
local Real = constant.pattern

local function make_parser(context)
    local function make_real(from, value, to)
        to = to - 1
        local positional = make_positional(context.input, from, to)
        value = tonumber(value)
        return logic.make_value(value, positional)
    end

    local parser = context:Cp() * Real * context:Cp() * Space / make_real
    return parser
end

return make_parser
