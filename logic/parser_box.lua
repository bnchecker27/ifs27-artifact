---
--- Box formula placeholder: the unicode "□" (U+25A1) or the escape
--- sequence "\box" produce a logic.make_box leaf node.  Boxes keep a
--- formula syntactically valid while it is being built up through the
--- formula-tree editor; semantic validation marks them incomplete.
---

local lpeg = require "lpeg"
local logic = require "logic.logic"
local make_positional = require "lib.positional"

local Space = lpeg.S(" \n\t")^0

-- U+25A1 WHITE SQUARE is the UTF-8 sequence \xE2\x96\xA1; the ASCII
-- alternative "\box" lets keyboard-only input produce the same node.
local BoxLit = lpeg.P("\226\150\161") + (lpeg.P("\\") * lpeg.P("box"))

local function make_parser(context)
    local function make_box(from, to)
        return logic.make_box(make_positional(context.input, from, to - 1))
    end
    return context:Cp() * BoxLit * context:Cp() * Space / make_box
end

return make_parser
