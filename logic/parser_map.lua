---
---

local logic = require "logic.logic"
local lpeg_util = require "lib.lpeg_util"
local lpeg = require "lpeg"
local parsing_context = require "lib.parsing_context"
local make_positional = require "lib.positional"
local parser_identifier = require "logic.parser_identifier"

local Space, Open, Close, Bar = lpeg_util.Space, lpeg_util.Open, lpeg_util.Close, lpeg_util.Bar

local MapName = "MAP" * Space

local function make_parser(aps, context)
    local function tostring_map(what)
        local result = {}
        table.insert(result, "MAP")
        table.insert(result, "(")
        local identifiers = what.operator.identifier_list or {}
        for _,identifier in ipairs(identifiers) do
            table.insert(result, tostring(identifier))
            table.insert(result, ",")
        end
        result[#result] = nil
        if what.operator.has_condition then
            local cond = what.children[#what.children]
            table.insert(result, "|")
            table.insert(result, tostring(cond))
        end
        table.insert(result, ")")
        result = table.concat(result)
        return result
    end

    local function make_map(pos_from, identifier_nodes, cond, pos_to)
        pos_to = pos_to - 1
        local children = {}
        local names = {}
        for _, node in ipairs(identifier_nodes or {}) do
            table.insert(children, node)
            table.insert(names, node:get_identifier())
        end
        if cond then
            table.insert(children, cond)
        end
        local map_op = {
            is_operator=true,
            name="map",
            arity=#children,
            precedence=7,
            notation="postfix",
            associativity="none",
            associative=false,
            identifier_list=names,
            has_condition=(cond ~= nil),
        }
        map_op.tostring = tostring_map
        local positional = make_positional(context.input, pos_from, pos_to)
        return logic.make_operator(children, map_op, positional)
    end

    local function make_map_cond(pos_from, identifier_nodes, aps, pos_to)
        return make_map(pos_from, identifier_nodes, aps, pos_to)
    end

    local function make_map_uncond(pos_from, identifier_nodes, pos_to)
        return make_map(pos_from, identifier_nodes, nil, pos_to)
    end

    local OpenOrError = lpeg_util.labeled(Open, "expected_lparen", {kw="("})
    local CloseOrError = lpeg_util.labeled(Close, "expected_rparen", {kw=")"})
    -- the evidence bar is a separator note stamped owner="MAP", so the
    -- operand-chain walk stops there (only P's bar continues)
    local BarOrError = lpeg_util.labeled(
        lpeg_util.sug_scope(
            lpeg_util.sep_note(lpeg.P"|", "pbar") * Space,
            {owner = "MAP"}),
        "expected_bar", {kw="|"})
    -- the namelist is a MAP-owned slot: its entries journal as atoms so
    -- the operand walk sees them, and payloads inside know only model
    -- variable names are candidates there
    local Identifier = lpeg_util.marked(parser_identifier(context),
                                        "atom")
    local IdentifierList = lpeg_util.make_list_parser(Identifier,
                                                      context:Label("expected_identifier")
                         + parsing_context.Suggest(nil, {cat="variable"}))
    local NameList = lpeg_util.sug_scope(IdentifierList,
                                         {owner = "MAP", slot = "any"})
    local Evidence = lpeg_util.sug_scope(aps,
        {owner = "MAP", post_bar = true, slot = "bool"})

    local parser = context:Cp() * MapName * OpenOrError * NameList * BarOrError * Evidence * CloseOrError * context:Cp() / make_map_cond
                 + context:Cp() * MapName * OpenOrError * NameList * CloseOrError * context:Cp() / make_map_uncond
    return parser
end

return make_parser
