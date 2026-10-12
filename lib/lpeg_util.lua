---
---

local lpeg_util = {}

local lpeg = require("lpeg")
local util = require "lib.util"
local parsing_context = require "lib.parsing_context"
-- local utf8 = require("utf8")

---
-- utf8_S: A UTF-8 compatible alternative to lpeg.S.
--
-- Note: This function was developed with the assistance of AI (Gemini 3 Flash).
-- Unlike the native lpeg.S, which operates on a byte-level set, this version
-- iterates through UTF-8 codepoints to build a prioritized choice pattern
-- (ordered choice), ensuring multibyte characters are matched as single units.
--
-- @param char_string A string containing the characters for the set.
-- @return An LPeg pattern representing the set of UTF-8 characters.
---
function lpeg_util.utf8_S(char_string)
    local pattern = lpeg.P(false)
    for _, code in util.tokenise_unicode(char_string) do
        pattern = pattern + lpeg.P(code)
    end
    return pattern
end

function lpeg_util.string_array_S(char_string, parsing_result)
    local pattern = lpeg.P(false)
    for _, code in ipairs(char_string) do
        pattern = pattern + lpeg.P(code)
    end
    if parsing_result then
        pattern = pattern / parsing_result
    end
    return pattern
end


local Space = lpeg.S(" \n\t")^0
local Comma = "," * Space

local function new_list(item)
    return {item}
end

local function acc_list(list, item)
    table.insert(list, item)
    return list
end

local Identifier = lpeg.C((lpeg.R"az" + lpeg.R"AZ" + "_") * (lpeg.R"az" + lpeg.R"AZ" + "_" + lpeg.R"09")^0) * Space

-- labeled(pattern, label): `pattern` first, and when it fails register
-- `label` as the expectation before failing — `p + Label(l)`.  This is
-- the "OrError" idiom used throughout the grammar ("XOrError = X +
-- context:Label("expected_y")"): the suggestion machinery reports the
-- label at the farthest position, so every mandatory token/operand a
-- parse can die on should be wrapped this way.
-- An optional third argument registers a suggestion PAYLOAD at the same
-- position (see suggestable) — e.g. {kw=","} on a continuation comma
-- tells the suggester that "," itself is offerable here.
function lpeg_util.labeled(pattern, label, payload)
    if payload ~= nil then
        return pattern + parsing_context.Label(label)
                       + parsing_context.Suggest(nil, payload)
    end
    return pattern + parsing_context.Label(label)
end

-- suggestable(pattern, payload): like labeled(), but registers a
-- suggestion PAYLOAD table instead of an expectation label —
-- `p + Suggest(nil, mk)`.  `payload` may be a function receiving the
-- inner pattern's captures and returning the payload table.  Compose
-- with labeled() to keep the expectation label too:
--   labeled(suggestable(operand, mk), "expected_identifier")
-- The payload is only kept when the registration site is the farthest
-- failure position — stale branches' payloads are discarded.
-- A table payload may carry `mark` — an operand-end kind
-- ("atom"/"expr"/"kwexpr"/"modify") — which wraps `pattern` with
-- marked() so a successful match journals where the operand ended.
function lpeg_util.suggestable(pattern, payload)
    if type(payload) == "table" and payload.mark then
        pattern = lpeg_util.marked(pattern, payload.mark, payload.mkw)
    end
    return pattern + parsing_context.Suggest(nil, payload)
end

-- suggestable_cb(pattern, name, mk): the payload is computed from the
-- capture stored under `name` by an earlier lpeg.Cg — the Cmt's inner
-- pattern is lpeg.Cb(name), so mk receives that stored value.  When no
-- such capture exists the Cb fails and no payload is registered.
function lpeg_util.suggestable_cb(pattern, name, mk)
    return pattern + parsing_context.Suggest(lpeg.Cb(name), mk)
end

-- suggestable_after(pattern, mk): like suggestable_cb but reads the
-- distinguished "sug_after" capture — the AST node of the operand that
-- most recently completed (see track).  mk receives the node or nil and
-- returns the payload; used by continuation/delimiter annotations whose
-- offer depends on what precedes them (e.g. ")" inside P(..) is only
-- offerable when the argument is a claim or a marginal term).
function lpeg_util.suggestable_after(pattern, mk)
    return pattern + parsing_context.Suggest(lpeg.Cb("sug_after")
                                             + lpeg.Cc(nil), mk)
end

-- track(pattern): bind the distinguished "sug_after" capture to the
-- node `pattern` produces — `Cg(patt) * Cb`, so the capture stream is
-- unchanged.  Every operand position (layer operands, atoms, groups)
-- wraps its production this way, so at any continuation position
-- Cb("sug_after") yields the AST node whose text ends there.
function lpeg_util.track(pattern)
    return lpeg.Cg(pattern, "sug_after") * lpeg.Cb("sug_after")
end

-- sug_scope(pattern, fields): push a scoped suggestion environment for
-- the duration of `pattern` — fields ⊆ {slot, role, owner, in_p, cond,
-- brole}.  A field set to `false` clears the inherited value; a
-- function value is called as f(ambient_env, pos) at push time (return
-- false to clear).  Payloads registered inside get stamped with the
-- env (parsing_context.suggest), so the resolver reads "bool-rhs
-- inside P's parens" instead of reconstructing it from the input.
-- The env pops on both success and failure, so stale scopes never leak
-- into sibling alternatives.
function lpeg_util.sug_scope(pattern, fields)
    local push = lpeg.Cmt(lpeg.P(true), function(_, pos)
        local ctx = parsing_context.get_current()
        if ctx then
            local f = {}
            for k, v in pairs(fields) do
                if type(v) == "function" then v = v(ctx.sug_env, pos) end
                f[k] = v
            end
            ctx:push_env(f)
        end
        return true
    end)
    local function pop()
        local ctx = parsing_context.get_current()
        if ctx then ctx:pop_env() end
        return true
    end
    local pop_ok = lpeg.Cmt(lpeg.P(true), pop)
    local pop_fail = lpeg.Cmt(lpeg.P(true), function(...)
        pop(...)
        return false
    end)
    return push * pattern * pop_ok + pop_fail
end

-- sug_scope_src(pattern, capname, fields): like sug_scope, but the
-- push runs where a Cg(capname) binding is live — the bound value (the
-- just-parsed source/selector AST) is stored as the env's `src`, so
-- payloads inside can name the governing term ("MUX(S, …" keys are
-- S's outcomes).  Nested owners re-push their own src; the outer env
-- was captured at push time, so shadowing never corrupts it.
function lpeg_util.sug_scope_src(pattern, capname, fields, key)
    local push = lpeg.Cmt(lpeg.Cb(capname) + lpeg.Cc(nil),
        function(_, pos, v)
        local ctx = parsing_context.get_current()
        if ctx then
            local f = {[key or "src"] = v}
            for k, val in pairs(fields) do
                if type(val) == "function" then
                    val = val(ctx.sug_env, pos)
                end
                f[k] = val
            end
            ctx:push_env(f)
        end
        return true
    end)
    local function pop()
        local ctx = parsing_context.get_current()
        if ctx then ctx:pop_env() end
        return true
    end
    local pop_ok = lpeg.Cmt(lpeg.P(true), pop)
    local pop_fail = lpeg.Cmt(lpeg.P(true), function(...)
        pop(...)
        return false
    end)
    return push * pattern * pop_ok + pop_fail
end

-- note(mk): a non-consuming pattern appending a record to the
-- context's match journal; mk(pos) -> record.
function lpeg_util.note(mk)
    return lpeg.Cmt(lpeg.P(true), function(_, pos)
        local ctx = parsing_context.get_current()
        if ctx then ctx:note(mk(pos)) end
        return true
    end)
end

-- sep_note(pattern, kind, extra): record a separator note when
-- `pattern` matches — the pattern is the operator token WITHOUT its
-- trailing Space, so the note's `to` is the token's end byte and
-- `from` its start.  `extra` is a table merged into the record, or a
-- function extra(pos, captures...) returning one.  The pattern's own
-- captures pass through so op symbols still reach `with_op`'s fold.
function lpeg_util.sep_note(pattern, kind, extra)
    return lpeg.Cmt(lpeg.Cp() * pattern, function(_, pos, from, ...)
        local ctx = parsing_context.get_current()
        if ctx then
            local rec = {kind = kind, from = from, to = pos}
            local ex = type(extra) == "function" and extra(pos, ...) or extra
            if ex then
                for k, v in pairs(ex) do rec[k] = v end
            end
            ctx:note(rec)
        end
        return true, ...
    end)
end

-- sep_note variant that drops the pattern's captures — for separators
-- folded into a list where the symbol itself is not collected
function lpeg_util.sep_note_silent(pattern, kind, extra)
    return lpeg.Cmt(lpeg.Cp() * pattern, function(_, pos, from, ...)
        local ctx = parsing_context.get_current()
        if ctx then
            local rec = {kind = kind, from = from, to = pos}
            local ex = type(extra) == "function" and extra(pos, ...) or extra
            if ex then
                for k, v in pairs(ex) do rec[k] = v end
            end
            ctx:note(rec)
        end
        return true
    end)
end

-- marked(pattern, okind, mkw): append an operand-end journal note when
-- `pattern` matches, carrying the AST node it produced.  The note is
-- emitted via a Cmt so it fires at match time (a `/fn` side-effect
-- would be discarded with a failed branch's unevaluated captures).
-- The capture stream is unchanged: the Cmt yields the node onward.
-- okind ∈ {"atom","expr","kwexpr","modify","fold"}; mkw names the
-- keyword for kwexpr nodes ("DIST","RENAME","MUX","PDIST","MOMENT"...).
function lpeg_util.marked(pattern, okind, kwname)
    return lpeg.Cmt(lpeg.Cp() * pattern * lpeg.Cp(),
        function(_, _, from, node, to)
            local ctx = parsing_context.get_current()
            if ctx then
                ctx:note{kind = "oend", okind = okind, kw = kwname,
                         node = node, from = from, to = to}
            end
            return true, node
        end)
end

-- The continuation comma of a list is a legal continuation wherever a
-- list can end, so its absence is labelled: the suggestion machinery then
-- offers "," after "MAP(Grade" or "[X : a = 0.5" as well.  The label sits
-- in a non-consuming suffix (Label + P(true)): the ^0 loop body itself
-- must never accept the empty string, which a Cmt label statically could.
function lpeg_util.make_list_parser(ItemParser, item_error)
    local Item = ItemParser
    if item_error then
        Item = ItemParser + item_error
    end
    -- the continuation comma journals a separator note (the slot after
    -- a comma is a fresh "any" operand position)
    local NotedComma = lpeg_util.sep_note_silent(lpeg.P",", "comma",
                                                 {nslot = "any"})
                       * Space
    return Item / new_list * (NotedComma * Item % acc_list)^0
         * (parsing_context.Label("expected_comma")
            + parsing_context.Suggest(nil, {kw = ","})
            + lpeg.P(true))
end

lpeg_util.IdentifierList = lpeg_util.make_list_parser(Identifier)

lpeg_util.Space = Space
lpeg_util.Open = "(" * lpeg_util.Space
lpeg_util.Close = ")" * lpeg_util.Space
lpeg_util.Bar = "|" * lpeg_util.Space
lpeg_util.Comma = Comma

lpeg_util.LBrack = "[" * Space
lpeg_util.RBrack = "]" * Space
lpeg_util.Colon = ":" * Space

lpeg_util.Identifier = Identifier
lpeg_util.Real = lpeg.C(lpeg.P"-"^-1 * lpeg.R("09")^1 * ("." * lpeg.R("09")^1)^-1) * Space
lpeg_util.LBrack = "[" * Space
lpeg_util.RBrack = "]" * Space

return lpeg_util
