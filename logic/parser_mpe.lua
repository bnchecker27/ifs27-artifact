---
---

local logic = require "logic.logic"
local lpeg_util = require "lib.lpeg_util"
local lpeg = require "lpeg"
local make_positional = require "lib.positional"

local Space, Open, Close = lpeg_util.Space, lpeg_util.Open, lpeg_util.Close

local MpeName = "MPE" * Space

local function make_parser(aps, context)
    local function make_mpe(pos_from, cond, pos_to)
        pos_to = pos_to - 1
        local children = {}
        if cond then
            table.insert(children, cond)
        end
        local mpe_op = {
            is_operator=true,
            name="mpe",
            arity=#children,
            precedence=7,
            notation="postfix",
            associativity="none",
            associative=false,
            has_condition=(cond ~= nil),
        }
        function mpe_op.tostring(what)
            local result = {}
            table.insert(result, "MPE")
            table.insert(result, "(")
            if #what.children > 0 then
                table.insert(result, tostring(what.children[1]))
            end
            table.insert(result, ")")
            return table.concat(result)
        end
        local positional = make_positional(context.input, pos_from, pos_to)
        return logic.make_operator(children, mpe_op, positional)
    end

    local OpenOrError = lpeg_util.labeled(Open, "expected_lparen", {kw="("})
    local CloseOrError = lpeg_util.labeled(Close, "expected_rparen", {kw=")"})

    -- MPE may be unconditional (empty body, no evidence) or conditional.
    -- The lookahead (#lpeg.P(")")) keeps MPE( from matching the empty
    -- alternative when the user is still typing a condition, so completion
    -- for MPE( still reports expected_phi / expected_compare etc.
    -- the condition is a Boolean-claim slot owned by MPE
    local OptionalCond = (#lpeg.P(")") / function() return nil end)
        + lpeg_util.sug_scope(aps, {slot = "bool", owner = "MPE"})

    local parser = context:Cp() * MpeName * OpenOrError * OptionalCond * CloseOrError * context:Cp() / make_mpe
    return parser
end

return make_parser
