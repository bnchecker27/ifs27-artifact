---
---

local lpeg = require "lpeg"
local logic = require "logic.logic"
local make_positional = require "lib.positional"

local Space = lpeg.S(" \n\t")^0

local function is_not_reserved(_, _, identifier)
    if identifier == "true" or identifier == "false" then
        return false
    end
    return true, identifier
end

-- the first character must not be a digit, otherwise `0` would lex as
-- an identifier and numeric comparisons like `0 = 0` would be claimed
-- by the variable-comparison parse before the number parser sees them
local IdentifierChars = (lpeg.R"az" + lpeg.R"AZ" + "_") * (lpeg.R"az" + lpeg.R"AZ" + "_" + lpeg.R"09")^0
local Identifier = lpeg.Cmt(lpeg.C(IdentifierChars), is_not_reserved)

-- the same word without the reserved-word filter: outcome-name slots
-- (comparison right sides, update/DIST/MUX/RENAME keys and values) take
-- literal names, and "true"/"false" are ordinary outcomes there —
-- andes-style domains are spelled {false, true}
local IdentifierLiteral = lpeg.C(IdentifierChars)

-- the box placeholder (□ or \box) is also accepted wherever an identifier
-- is expected — comparisons, MAP query lists, IDP/INFL arguments — so a
-- partially built formula stays parseable while a slot is unfilled
local BoxLit = lpeg.P("\226\150\161") + (lpeg.P("\\") * lpeg.P("box"))


local function make_parser(context, allow_reserved)
    local function make_identifier(from, identifier, to)
        to = to - 1
        local positional = make_positional(context.input, from, to)
        if identifier == "\226\150\161" or identifier == "\\box" then
            return logic.make_box(positional)
        end
        return logic.make_identifier(identifier, positional)
    end

    local word = allow_reserved and IdentifierLiteral or Identifier
    local parser = context:Cp() * (word + lpeg.C(BoxLit)) * context:Cp() * Space / make_identifier
    return parser
end

return make_parser
