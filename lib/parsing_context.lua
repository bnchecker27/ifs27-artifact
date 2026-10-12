---
---

local util = require "lib.util"
local lpeg = require "lpeg"

-- The patterns created by this module (Cp/Label/Ci) do not close over the
-- context table.  Instead they read a shared "current" context, which is
-- set by parser_bn_logic for each call.  This keeps the patterns identical
-- across parse invocations and lets the parser update the context associated
-- with the current input.
local current_context = nil

local function get_context()
    return current_context
end

local function set_context(ctx)
    current_context = ctx
end

local function expect_label_fn(label)
    return function(_, pos)
        local ctx = get_context()
        if ctx then
            ctx:expect(pos, label)
        end
        return nil
    end
end

-- A Suggest pattern fails unconditionally after registering a payload
-- table at the current position — the suggestion-directed analogue of
-- Label.  `patt` is the Cmt's inner pattern (P(true) for none; e.g.
-- lpeg.Cb("name") to feed a stored capture); `mk` may be a function
-- receiving that pattern's captures and returning the payload table,
-- letting an annotation carry dynamic data like a left operand's name.
local function suggest_fn(mk)
    return function(_, pos, ...)
        local ctx = get_context()
        if ctx then
            local p = type(mk) == "function" and mk(...) or mk
            ctx:suggest(pos, p)
        end
        return nil
    end
end

local function make_suggest(patt, mk)
    return lpeg.Cmt(patt or lpeg.P(true), suggest_fn(mk))
end

local function progress_fn(_, pos)
    local ctx = get_context()
    if ctx then
        ctx:progress(pos)
    end
    return true
end

-- A Note pattern succeeds without consuming after appending a record to
-- the context's match journal.  `inner` captures feed `mk` —
-- mk(pos, captures...) -> record — so a note can carry positions or a
-- captured AST.  The journal is the resolver's structural memory: which
-- operands completed where, which operator tokens it passed — the
-- information the old text-scanning position classifier reconstructed
-- by re-reading the input backwards.
local function note_fn(mk)
    return function(_, pos, ...)
        local ctx = get_context()
        if ctx then
            ctx:note(mk(pos, ...))
        end
        return true
    end
end

local function make_note(inner, mk)
    return lpeg.Cmt(inner or lpeg.P(true), note_fn(mk))
end

-- A Label pattern fails unconditionally after registering `label` as an
-- expectation at the current position.  It is a plain constructor (no
-- context needed at construction time) so utility modules can build
-- labelled alternatives as well.
local function make_label(label)
    return lpeg.Cmt(lpeg.P(true), expect_label_fn(label))
end

local function make_parsing_context(input)
    local context = {}
    context.input = input
    context.last_position = 0
    -- all labels registered at the farthest position, in registration
    -- order: several parser alternatives can legitimately expect different
    -- continuations at the same spot (e.g. "P(Grade" expects a compare
    -- operator, "|" and ")"), so the farthest-position set is a UNION, not
    -- a single winner.
    context.expected_labels = nil
    -- suggestion payloads registered at the farthest position, same
    -- union-at-max discipline as expected_labels: entries recorded at
    -- earlier positions are stale branches and get discarded
    context.suggest_list = nil
    -- labels and payloads interleaved in registration order —
    -- {label=…} / {suggest=…} entries; the resolver emits its offer
    -- list in this order, which is the grammar's alternative order
    context.order_list = nil
    -- the suggestion journal: notes appended in match order — operand
    -- ends ({kind="oend"}), operator separators ("sep"/"psep"/"csep"/
    -- "pbar") — consumed by the resolver to reconstruct the operand
    -- chain instead of re-scanning the input.
    context.notes = {}
    -- the scoped suggestion environment: a linked list of tables with
    -- slot/role/owner fields, pushed while an operand parses and popped
    -- after it.  Payloads registered inside a scope are stamped with
    -- the env so the resolver knows e.g. "bool-rhs inside P's parens".
    context.sug_env = nil
    function context:note(rec)
        if self.sug_env then
            local e = self.sug_env
            rec.slot, rec.role = e.slot, e.role
            rec.owner, rec.in_p, rec.in_cond, rec.brole =
                e.owner, e.in_p or nil, e.cond or nil, e.brole
            rec.post_bar = e.post_bar or nil
            rec.depth = e.depth
            if e.src ~= nil then rec.src = e.src end
            if e.btarget ~= nil then rec.btarget = e.btarget end
        end
        local n = self.notes
        n[#n + 1] = rec
    end
    local ENV_KEYS = {"slot", "role", "owner", "in_p", "cond", "brole",
                      "post_bar", "src", "btarget"}
    -- fields.X = value sets, nil inherits the ambient value, false clears
    function context:push_env(fields)
        local p, e = self.sug_env, {}
        for _, k in ipairs(ENV_KEYS) do
            local v = fields[k]
            if v == nil then v = p and p[k]
            elseif v == false then v = nil end
            e[k] = v
        end
        e.prev = p
        e.depth = (p and p.depth or 0) + 1
        self.sug_env = e
    end
    function context:pop_env()
        self.sug_env = self.sug_env and self.sug_env.prev
    end
    function context:progress(new_position)
        if new_position > self.last_position then
            self.last_position = new_position
            self.expected_labels = nil
            self.suggest_list = nil
            self.order_list = nil
        end
    end
    function context:expect(pos, label)
        if pos > self.last_position then
            self.last_position = pos
            self.expected_labels = {label}
            self.suggest_list = nil
            self.order_list = {{label = label}}
        elseif pos == self.last_position then
            local el = self.expected_labels
            if not el then
                self.expected_labels = {label}
                self.order_list = {{label = label}}
            else
                for i = 1, #el do
                    if el[i] == label then return nil end
                end
                el[#el + 1] = label
                self.order_list[#self.order_list + 1] = {label = label}
            end
        end
        return nil
    end
    function context:suggest(pos, payload)
        if payload ~= nil and self.sug_env then
            -- stamp the ambient scope onto the payload — copy first,
            -- since payload tables are often shared literals
            local e = self.sug_env
            local p2 = {}
            for k, v in pairs(payload) do p2[k] = v end
            p2.slot, p2.role = e.slot, e.role
            p2.owner, p2.in_p, p2.in_cond, p2.brole =
                e.owner, e.in_p or nil, e.cond or nil, e.brole
            p2.post_bar = e.post_bar or nil
            p2.depth = e.depth
            if e.src ~= nil then p2.src = e.src end
            if e.btarget ~= nil then p2.btarget = e.btarget end
            payload = p2
        end
        if pos > self.last_position then
            self.last_position = pos
            self.expected_labels = nil
            self.suggest_list = {payload}
            self.order_list = {{suggest = payload}}
        elseif pos == self.last_position then
            local sl = self.suggest_list
            if sl then sl[#sl + 1] = payload
            else self.suggest_list = {payload} end
            if self.order_list then
                self.order_list[#self.order_list + 1] = {suggest = payload}
            else
                self.order_list = {{suggest = payload}}
            end
        end
        return nil
    end
    function context:Label(label)
        return make_label(label)
    end
    function context:Cp()
        return lpeg.Cp() * lpeg.P(progress_fn)
    end
    function context:Ci()
        return lpeg.P(progress_fn)
    end
    function context:get_last_position()
        return self.last_position
    end
    -- re-arm the context for another input: a grammar closes over this
    -- object (context.input is read at match time inside captures), so
    -- resetting it here lets a built grammar be reused across inputs
    -- instead of being rebuilt per parse
    function context:reset(new_input)
        self.input = new_input
        self.last_position = 0
        self.expected_labels = nil
        self.suggest_list = nil
        self.order_list = nil
        self.notes = {}
        self.sug_env = nil
        self.index = nil
    end
    -- returns the ordered list of labels expected at the farthest
    -- position (or nil when none was registered)
    function context:get_expected()
        return self.expected_labels
    end
    -- suggestion payloads at the farthest position (nil when none)
    function context:get_suggest()
        return self.suggest_list
    end
    -- labels and payloads at the farthest position, interleaved in
    -- registration order ({label=…}/{suggest=…} entries)
    function context:get_order()
        return self.order_list
    end
    -- the suggestion journal (operand-end / separator notes)
    function context:get_notes()
        return self.notes
    end
    function context:get_line_and_column()
        return util.index_to_line_and_column(self.input, self.index)
    end
    return context
end

local M = {}
setmetatable(M, {__call = function(_, input) return make_parsing_context(input) end})
M.set_current = set_context
M.get_current = get_context
M.Label = make_label
M.Suggest = make_suggest
M.Note = make_note
return M
