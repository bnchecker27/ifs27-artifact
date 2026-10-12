---
--- logic/constant.lua — the numeric-constant grammar, shared by the
--- formula parser (logic/parser_real.lua) and the demonstrator UI's
--- constant-entry dialog so the accepted syntax lives in exactly one
--- place.  LuaJIT / Lua 5.4 common subset.
---

local lpeg = require "lpeg"

local M = {}

-- captures the matched text: optional '-', integer digits, optional
-- fractional part.  parser_real embeds this pattern into its grammar;
-- the UI calls is_valid for whole-string acceptance.
M.pattern = lpeg.C(lpeg.P"-"^-1 * lpeg.R("09")^1 * ("." * lpeg.R("09")^1)^-1)

local full = M.pattern * -1

function M.is_valid(s)
    return type(s) == "string" and #s > 0 and full:match(s) ~= nil
end

return M
