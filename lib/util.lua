---
---

if not utf8 then
    _, utf8 = pcall(require, 'lua-utf8')
end

local tostring_old = tostring

tostring = function(a, ...)
    local mt = getmetatable(a)
    if mt and mt.__tostring then
        return mt.__tostring(a, ...)
    else
        return tostring_old(a)
    end
end

local util = {}
local utf8

local ffi = require "ffi"
ffi.cdef [[void *malloc(size_t size);]]
ffi.cdef [[void free(void *ptr);]]
ffi.cdef [[void *realloc(void *ptr, size_t size);]]

local function vector_to_string(self)
    local result = {}
    table.insert(result, "[")
    for i = 0, self.size_val - 1 do
        table.insert(result, tostring(self.data_ptr[i]))
        table.insert(result, ",")
    end
    if result[#result] == "," then
        result[#result] = nil
    end
    table.insert(result, "]")
    return table.concat(result)
end

local existing_vector_types = {}
existing_vector_types = {}

function util.get_vector_type_name(base_type, auto_free)
    return ([[vector_%s_%s_t]]):format(base_type, auto_free)
end

function util.get_vector_metatype(base_type, auto_free)
    auto_free = util.toboolean(auto_free)

    local type_name = util.get_vector_type_name(base_type, auto_free)
    local vector_ctype = existing_vector_types[type_name]
    if not vector_ctype then
        ffi.cdef(([[
        typedef struct {
          %s *data_ptr;
          unsigned reserved_val;
          unsigned size_val;
        } %s;
        ]]):format(base_type, type_name))
        local mt = {}
        mt.__tostring = vector_to_string
        local element_size = ffi.sizeof(base_type)
        local vector_functions = {
            allocate = function(self)
                self.data_ptr = ffi.C.malloc(element_size)
                self.reserved_val = 1
                self.size_val = 0
            end,

            free = function(self)
                ffi.C.free(self.data_ptr)
            end,

            push = function(self, what)
                if self.size_val + 1 > self.reserved_val then
                    self.reserved_val = self.reserved_val * 2
                    self.data_ptr = ffi.C.realloc(self.data_ptr, element_size * self.reserved_val)
                end
                self.data_ptr[self.size_val] = what
                self.size_val = self.size_val + 1
            end,

            top = function(self)
                return self.data_ptr[self.size_val - 1]
            end,

            pop = function(self)
                result = self.data_ptr[self.size_val - 1]
                self.size_val = self.size_val - 1
                return result
            end,

            size = function(self)
                return self.size_val
            end,

            empty = function(self)
                return self.size_val == 0
            end,

            push_back = function(self, what)
                if self.size_val + 1 > self.reserved_val then
                    self.reserved_val = self.reserved_val * 2
                    self.data_ptr = ffi.C.realloc(self.data_ptr, element_size * self.reserved_val)
                end
                self.data_ptr[self.size_val] = what
                self.size_val = self.size_val + 1
            end,

            pop_back = function(self)
                result = self.data_ptr[self.size_val - 1]
                self.size_val = self.size_val - 1
                return result
            end,

            data = function(self)
                return self.data_ptr
            end,

            resize = function(self, new_size)
                if new_size <= self.size_val then
                    self.size_val = new_size
                elseif new_size <= self.reserved_val then
                    for i = self.size_val, new_size - 1 do
                        self.data_ptr[i] = 0
                    end
                    self.size_val = new_size
                else
                    local new_reseved = 1
                    while new_reseved < new_size do
                        new_reseved = new_reseved * 2
                    end
                    self.data_ptr = ffi.C.realloc(self.data_ptr, element_size * new_reseved)
                    self.reserved_val = new_reseved
                    self.size_val = new_size
                end
            end
        }

        if auto_free then
            mt.__gc = vector_functions.free
        end

        mt.__index = function(self, index)
            if type(index) == "string" then
                return vector_functions[index]
            end
            return self.data_ptr[index]
        end

        mt.__newindex = function(self, index, value)
            self.data_ptr[index] = value
        end
        vector_ctype = ffi.metatype(type_name, mt)
        existing_vector_types[type_name] = vector_ctype
    end
    return vector_ctype
end

function util.new_vector(base_type, auto_free)
    local vector_ctype = util.get_vector_metatype(base_type, auto_free)
    local result = vector_ctype()
    result:allocate()
    return result
end

function util.index_to_line_and_column(str, index)
    -- produced by Google Gemini AI, adapted
    if index > #str then
        index = #str
    end
    if index < 1 then
        index = 1
    end

    local line = 1
    local col = 1

    for i = 1, index - 1 do
        local char = str:sub(i, i)
        if char == "\n" then
            line = line + 1
            col = 1
        else
            col = col + 1
        end
    end

    return line, col
end

function util.fix_path()
    local path = util.split(package.path, ";")
    table.insert(path, "./?/init.lua")
    package.path = table.concat(path, ";")
end

function util.read_from_file(fn)
    assert(fn)
    local file
    if type(fn) == "string" then
        _, file = pcall(io.open, fn, "r")
        if not file then
            return nil
        end
    else
        file = fn
    end
    local result = file:read("*all")
    file:close()
    return result
end

function util.dump_to_file(s, file)
    assert(file)
    if type(file) == "string" then
        _, file = pcall(io.open, file, "w")
    end
    assert(file)
    file:write(s)
    file:close()
end

function util.file_exists(filename)
    local _, file = pcall(io.open, filename, "r")
    if not file then
        return false
    else
        file:close()
        return true
    end
end

function util.split(splitWhat, inSplitPattern)
    assert(type(splitWhat) == "string", type(splitWhat))
    assert(type(inSplitPattern) == "string", type(inSplitPattern))
    local outResults = {}
    local theStart = 1
    local theSplitStart, theSplitEnd = string.find(splitWhat, inSplitPattern, theStart)
    while theSplitStart do
        table.insert(outResults, string.sub(splitWhat, theStart, theSplitStart - 1))
        theStart = theSplitEnd + 1
        theSplitStart, theSplitEnd = string.find(splitWhat, inSplitPattern, theStart)
    end
    table.insert(outResults, string.sub(splitWhat, theStart))
    return outResults
end

function util.trim(s)
    assert(type(s) == "string", type(s))
    return (string.gsub(s, "^%s*(.-)%s*$", "%1"))
end

function util.remove_whitespace(s)
    assert(type(s) == "string")
    return s:gsub("%s+", "")
end

function util.replace_string_table(input, replacements)
    assert(type(input) == "string", type(input))
    assert(type(replacements) == "table", type(replacements))
    for key, value in pairs(replacements) do
        assert(type(key) == "string", type(key))
        assert(type(value) == "string", type(value))
    end
    local result = {}
    local max_replace_length = 0
    for substring, _ in pairs(replacements) do
        if #substring > max_replace_length then
            max_replace_length = #substring
        end
    end
    local index = 1
    while index <= #input do
        local index_end = index
        local replacement
        while not replacement and (index_end - index + 1 <= max_replace_length) do
            local substring = input:sub(index, index_end)
            replacement = replacements[substring]
            if not replacement then
                index_end = index_end + 1
            end
        end
        if not replacement then
            replacement = input:sub(index, index)
            index = index + 1
        else
            index = index_end + 1
        end
        table.insert(result, replacement)
    end
    return table.concat(result)
end

local charset = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890"

function util.random_string(length)
    assert(type(length) == "number")
    local result = {}
    for _ = 1, length do
        local random_number = math.random(1, #charset)
        table.insert(result, charset:sub(random_number, random_number))
    end
    return table.concat(result, "")
end

function util.random_filename(ending)
    assert(type(ending) == "string")
    return util.random_string(50) .. "." .. ending
end

function util.toboolean(value)
    if value then
        return true
    else
        return false
    end
end

function util.load_string(value)
    assert(type(value) == "string")
    if loadstring then
        value = loadstring(value)
    else
        value = load(value)
    end
    assert(value)
    return value
end

function util.reverse_list(x)
    assert(type(x) == "table")
    local rev = {}
    for i = #x, 1, -1 do
        rev[#rev + 1] = x[i]
    end
    return rev
end

function util.count_entries(t)
    assert(type(t) == "table", type(t))
    local result = 0
    for _, _ in pairs(t) do
        result = result + 1
    end
    return result
end

function util.shallow_copy(from, to)
    assert(type(from) == "table" or type(from) == "nil")
    if not from then
        return nil
    end
    assert(type(from) == "table")
    assert(type(to) == "nil" or type(to) == "table")
    if not to then
        to = {}
    end
    for key, value in pairs(from) do
        to[key] = value
    end
    return to
end

function util.deep_copy(from, to)
    assert(type(to) == "nil" or type(to) == "table")
    assert(type(from) ~= "function")
    assert(type(from) ~= "thread")
    assert(type(from) ~= "userdata")
    if not to then
        if type(from) == "nil" or type(from) == "boolean" or type(from) == "number" or type(from) == "string" then
            return from
        end
        assert(type(from) == "table")
        local result = {}
        for key, value in pairs(from) do
            result[util.deep_copy(key)] = util.deep_copy(value)
        end
        return result
    else
        local dc_result = util.deep_copy(from)
        for key, value in pairs(dc_result) do
            to[key] = value
        end
        return to
    end
end

function util.table_empty(t)
    assert(type(t) == "table")
    return next(t) == nil
end

function util.merge_tables(...)
    local tables = { ... }
    local result = {}
    for _, tab in ipairs(tables) do
        assert(type(tab) == "table", "All parameters must be tables: " .. tostring(tab))
        for k, v in pairs(tab) do
            result[k] = v
        end
    end
    return result
end

function util.split_trim(what)
    assert(type(what) == "string", type(what))
    what = util.split(what, ",")
    for i = 1, #what do
        what[i] = util.trim(what[i])
    end
    return what
end

local js = {}

function util.js_set(name, value)
    js[name] = value
end

function util.js_get(name)
    local eval = js["eval"]
    if js[name] then
        return js[name]
    elseif eval then
        return eval(name)
    else
        return nil
    end
end

local js_post_message

function util.set_js_post_message(new_js_post_message)
    js_post_message = new_js_post_message
end

function util.get_js_post_message()
    return js_post_message
end

function util.js_post_message(message)
    js_post_message(message)
end

local js_intl_segmenter

function util.set_js_intl_segmenter(new_js_intl_segmenter)
    js_intl_segmenter = new_js_intl_segmenter
end

local icu_tool_lib
--require "lib.icu_tool"

local function is_icu_command_lib_available()
    local status
    status, icu_tool_lib = pcall(package.loadlib, "/home/author/svn/l-and-m/lua/lib/icu_tool.so", "luaopen_lib_icu_tool")
    if not status then
        return false
    end
    status, icu_tool_lib = pcall(icu_tool_lib)

    if not status then
        return false
    end
    assert(type(icu_tool_lib) == "table", icu_tool_lib)
    assert(icu_tool_lib.tokenise_unicode)
    return true
end

local function is_js_intl_segmenter_available()
    if not js_intl_segmenter then
        return false
    end
    return true
end


local function is_icu_lua53_utf8_available()
    _, utf8 = pcall(require, "utf8")
    if type(utf8) ~= "table" then
        return false
    end
    return true
end

local function tokenise_unicode_icu_lib(str)
    if str == "" then
        return {}
    end
    return icu_tool_lib.tokenise_unicode(str)
end

local function tokenise_unicode_js_intl_segmenter(str)
    local segments = util.js_get("Array.from")(js_intl_segmenter.segment(str))
    local result = {}
    for i = 0, segments.length - 1 do
        table.insert(result, segments.at(i).segment)
    end
    return result
end

local function tokenise_unicode_lua53_utf8(str)
    local result = {}
    for _, p in utf8.codes(str) do
        table.insert(result, utf8.char(p))
    end
    return result
end

function util.tokenise_unicode(str)
    if is_icu_command_lib_available() then
        return tokenise_unicode_icu_lib(str)
    elseif is_js_intl_segmenter_available() then
        return tokenise_unicode_js_intl_segmenter(str)
    elseif is_icu_lua53_utf8_available() then
        return tokenise_unicode_lua53_utf8(str)
    else
        assert(false, "No unicode tokeniser library available")
    end
end

function util.len_unicode_graphemes(str)
    return #util.tokenise_unicode(str)
end

local queue_metatable = {
    what = "queue",
    __tostring = function(self)
        local result = {}
        for i = self.left_index, self.right_index do
            table.insert(result, tostring(self.content[i]))
        end
        return "{" .. table.concat(result, ",") .. "}"
    end
}

local function is_queue(what)
    if not what then
        return false
    end
    local metatable = getmetatable(what)
    if not metatable then
        return false
    end
    if metatable.what ~= "queue" then
        return false
    end
    return true
end

function util.make_queue()
    local queue = { left_index = 1, right_index = 0, content = {} }

    function queue:insert_right(what)
        assert(is_queue(self))
        self.right_index = self.right_index + 1
        self.content[self.right_index] = what
    end

    function queue:insert_left(what)
        assert(is_queue(self))
        self.left_index = self.left_index - 1
        self.content[self.left_index] = what
    end

    function queue:remove_left()
        assert(is_queue(self))
        local result = self.content[self.left_index]
        self.content[self.left_index] = nil
        self.left_index = self.left_index + 1
        return result
    end

    function queue:remove_right()
        assert(is_queue(self))
        local result = self.content[self.right_index]
        self.content[self.right_index] = nil
        self.right_index = self.right_index - 1
        return result
    end

    function queue:empty()
        assert(is_queue(self))
        return self.right_index < self.left_index
    end

    function queue:len()
        assert(is_queue(self))
        return util.count_entries(self.content)
    end

    setmetatable(queue, queue_metatable)

    return queue
end

local stack_metatable = {
    what = "stack",
    __tostring = function(self)
        return "{" .. table.concat(tostring(self.content), ",") .. "}"
    end
}

function util.make_stack()
    local stack = { content = {} }

    function stack:push(what)
        table.insert(self.content, what)
    end

    function stack:top(where)
        if not where then
            where = 1
        end
        return self.content[#self.content - where + 1]
    end

    function stack:pop(num)
        if not num then
            num = 1
        end
        local result
        for _ = 1, num do
            result = self.content[#self.content]
            self.content[#self.content] = nil
        end
        return result
    end

    function stack:empty()
        return #self.content == 0
    end

    function stack:size()
        return #self.content
    end

    setmetatable(stack, stack_metatable)

    return stack
end

function util.make_ordered_set()
    local result = {}
    local list = {}
    local set = {}

    local metatable = {
        __tostring = function(_)
            local result = {}
            for _, value in ipairs(list) do
                table.insert(result, tostring(value))
            end
            return "{" .. table.concat(result, ",") .. "}"
        end,
        __index = function(_, index)
            return set[tostring(index)]
        end,
        __newindex = function(_, key, value)
            if value ~= nil then
                value = true
                if not set[tostring(key)] then
                    set[tostring(key)] = value
                    table.insert(list, key)
                end
            else
                error()
            end
        end,
        __pairs = function(what)
            local index = 0
            local function state_set_next(_, _)
                index = index + 1
                return list[index]
            end
            return state_set_next, what, nil
        end,
        __len = function(self)
            return #list
        end,
        __eq = function(a, b)
            if #a ~= #b then
                return false
            else
                for key, _ in pairs(a) do
                    if not b[key] then
                        return false
                    end
                end
                return true
            end
        end
    }

    setmetatable(result, metatable)
    return result
end

function util.ternary(cond, if_true, if_false)
    if cond then
        return if_true
    else
        return if_false
    end
end

local stopwatch_metatable = {
    __tostring = function(self)
        return tostring(self:get_elapsed())
    end
}

function util.make_stopwatch()
    local stopwatch = { elapsed = 0 }

    function stopwatch:start()
        assert(not self.started)
        self.started = os.time()
    end

    function stopwatch:stop()
        assert(self.started)
        self.elapsed = self.elapsed + os.time() - self.started
        self.started = nil
    end

    function stopwatch:get_elapsed()
        if self.started then
            return self.elapsed + os.time() - self.started
        else
            return self.elapsed
        end
    end

    setmetatable(stopwatch, stopwatch_metatable)

    return stopwatch
end

function util.list_to_set(list)
    local set = {}
    for _, entry in ipairs(list) do
        set[entry] = true
    end
    return set
end

function util.set_to_list(set)
    local list = {}
    for key, _ in pairs(set) do
        table.insert(list, key)
    end
    table.sort(list)
    return list
end

function util.set_intersection(set_1, set_2)
    local result = {}
    for key, _ in pairs(set_1) do
        if set_2[key] then
            result[key] = true
        end
    end
    return result
end

function util.keys_to_sorted(keys)
    local result = {}
    for key, _ in pairs(keys) do
        table.insert(result, key)
    end
    table.sort(result)
    return result
end

function util.append_arrays(...)
    local result = {}
    local tables = { ... }
    for _, array in ipairs(tables) do
        for _, value in ipairs(array) do
            table.insert(result, value)
        end
    end
    return result
end

function util.validate_numeric_parameter(value, param_name, max_value, allow_negative)
    if type(value) ~= "string" and type(value) ~= "number" then
        error({ key = "invalid_numeric_parameter", parameters = { parameter = param_name, value = tostring(value) } })
    end

    local num_value = tonumber(value)
    if not num_value then
        error({ key = "invalid_numeric_parameter", parameters = { parameter = param_name, value = tostring(value) } })
    end

    if not allow_negative and num_value < 0 then
        error({ key = "numeric_parameter_negative", parameters = { parameter = param_name, value = num_value } })
    end

    if max_value and num_value > max_value then
        error({ key = "numeric_parameter_too_large", parameters = { parameter = param_name, value = num_value, max = max_value } })
    end

    return num_value
end

-- Outcome spellings that carry a truth reading.  Tokens are matched on
-- letter runs after lowercasing, so embedded names like "res_yes" or
-- "__no__" classify by their token; a name containing BOTH a truthy and
-- a falsy token ("yes_no") is ambiguous and counts as neither.
local TRUTHY_TOKENS = {["true"] = true, ["t"] = true, ["yes"] = true,
                       ["y"] = true, ["on"] = true}
local FALSY_TOKENS  = {["false"] = true, ["f"] = true, ["no"] = true,
                       ["n"] = true, ["off"] = true}

local function token_class(name)
    local truthy, falsy = false, false
    for token in string.gmatch(string.lower(name), "%a+") do
        if TRUTHY_TOKENS[token] then truthy = true end
        if FALSY_TOKENS[token] then falsy = true end
    end
    if truthy == falsy then
        return nil
    end
    return truthy and "T" or "F"
end

-- the "true" outcome of a two-outcome Boolean-spelled domain
-- ({F,T}, {false,true}, {t,f}, {yes,no}, {res_yes,res_no}, ... — any
-- order, any case), nil otherwise.  Domains like {full,empty} or
-- {low,high} carry no truth spelling and stay nil, as do numeric
-- domains (digit-only names have no letter tokens).
function util.true_outcome(values)
    if type(values) ~= "table" or #values ~= 2 then
        return nil
    end
    local first = token_class(tostring(values[1]))
    local second = token_class(tostring(values[2]))
    if first == "T" and second == "F" then
        return values[1]
    end
    if first == "F" and second == "T" then
        return values[2]
    end
    return nil
end

function util.is_boolean_domain(values)
    return util.true_outcome(values) ~= nil
end

-- True when the Lua heap is past `kb_limit` even after a full collection —
-- collectgarbage("count") alone reports uncollected garbage, which produces
-- false trips right after a memory-heavy phase has bailed out.
function util.lua_heap_over(kb_limit)
    if collectgarbage("count") <= kb_limit then
        return false
    end
    collectgarbage("collect")
    return collectgarbage("count") > kb_limit
end

function util.validate_file_path(path)
    if type(path) ~= "string" then
        error({ key = "invalid_numeric_parameter", parameters = { parameter = "file_path", value = tostring(path) } })
    end

    -- Basic path traversal protection
    if path:find("%.%.") or path:find("/") == 1 then
        error({ key = "invalid_file_path", parameters = { path = path } })
    end

    return path
end

function util.translate_error(err)
    if type(err) == "string" then
        return err
    end
    assert(type(err) == "table", err)
    local key = err.key
    assert(key, err)
    local parameters = err.parameters or {}

    -- smiti18n is only installed inside the Docker image; outside it a
    -- bare require would mask the real error with a module-not-found
    -- traceback.  The locale file is a plain {en = {key = template}}
    -- table, so the fallback formats "%{name}" placeholders directly.
    local ok_i18n, i18n = pcall(require, 'smiti18n')
    local result
    if ok_i18n then
        -- Load locales (idempotent - safe to call multiple times)
        i18n.load(require 'locales.errors')
        i18n.setLocale('en')
        result = i18n(key, parameters) or key
    else
        local ok_loc, locales = pcall(require, 'locales.errors')
        local template = ok_loc and locales.en[key] or nil
        result = template and (template:gsub("%%{%s*([%w_]+)%s*}",
            function(param)
                local v = parameters[param]
                return v ~= nil and tostring(v) or ("%{" .. param .. "}")
            end)) or key
    end

    local positional = err.positional
    if positional then
        local from_line, from_column = positional:get_from_line_column()
        local to_line, to_column = positional:get_to_line_column()
        if not to_line then
            result = ([[%s (line: %d, column: %d)]]):format(result, from_line, from_column)
        else
            result = ([[%s (from line: %d, column: %d to line: %d, column: %d)]])
                :format(result, from_line, from_column, to_line, to_column)
        end
    end
    return result
end

return util
