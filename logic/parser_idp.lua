---
---

local logic = require "logic.logic"
local lpeg_util = require "lib.lpeg_util"
local lpeg = require "lpeg"
local make_positional = require "lib.positional"
local parser_identifier = require "logic.parser_identifier"

local Space, Open, Close, Bar, Comma = lpeg_util.Space, lpeg_util.Open, lpeg_util.Close, lpeg_util.Bar,
    lpeg_util.Comma

local IdpName = "IDP" * Space

local function make_parser(context)
    local function make_idp(pos_from, left, right, cond, pos_to)
        -- Fix parameter order issue: when cond is a number and pos_to is nil,
        -- it means the optional conditions weren't provided
        if type(cond) == "number" and pos_to == nil then
            pos_to = cond
            cond = {}
        end

        if pos_to then
            pos_to = pos_to - 1
        end
        if not cond then
            cond = {}
        end
        local function id_name(node)
            if node and node.get_identifier then
                return node:get_identifier()
            end
            return tostring(node)
        end
        local children = {}
        if left then table.insert(children, left) end
        if right then table.insert(children, right) end
        local cond_names = {}
        for _, c in ipairs(cond) do
            table.insert(children, c)
            table.insert(cond_names, id_name(c))
        end
        local idp_op = {
            is_operator=true,
            name="idp",
            arity=#children,
            precedence=7,
            notation="postfix",
            associativity="none",
            associative=false,
            left=id_name(left),
            right=id_name(right),
            cond=cond_names
        }

        function idp_op.tostring(what)
            local result = {}
            table.insert(result, "IDP")
            table.insert(result, "(")
            table.insert(result, tostring(what.operator.left))
            table.insert(result,",")
            table.insert(result, tostring(what.operator.right))
            if #what.operator.cond > 0 then
                table.insert(result,"|")
                local identifiers = what.operator.cond
                for _,identifier in ipairs(identifiers) do
                    table.insert(result, tostring(identifier))
                    table.insert(result, ",")
                end
                result[#result] = nil
            end
            table.insert(result, ")")
            result = table.concat(result)
            return result
        end
        local positional = make_positional(context.input, pos_from, pos_to)
        return logic.make_operator(children, idp_op, positional)
    end

    local OpenOrError = lpeg_util.labeled(Open, "expected_lparen", {kw="("})
    local CloseOrError = lpeg_util.labeled(Close, "expected_rparen", {kw=")"})
    local CommaOrError = lpeg_util.labeled(Comma, "expected_comma", {kw=","})
    local BarOrError = lpeg_util.labeled(
        lpeg_util.sug_scope(
            lpeg_util.sep_note(lpeg.P"|", "pbar", {nslot = "any"}) * Space,
            {owner = "IDP"}),
        "expected_bar", {kw="|"})
    -- the namelist slots take model variables only; each name journals
    -- as an operand atom
    local Identifier = lpeg_util.marked(parser_identifier(context),
                                        "atom")
    local IdentifierOrError = lpeg_util.labeled(Identifier, "expected_identifier", {cat="variable"})
    local IdentifierList = lpeg_util.make_list_parser(IdentifierOrError)
    local function Named(p)
        return lpeg_util.sug_scope(p, {owner = "IDP", slot = "any"})
    end

    local parser = context:Cp() * IdpName * OpenOrError * Named(IdentifierOrError) * CommaOrError * Named(IdentifierOrError) * (BarOrError * Named(IdentifierList))^-1 * CloseOrError * context:Cp() / make_idp
    return parser
end

return make_parser
