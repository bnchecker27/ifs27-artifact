-- Minimal JSON encode/decode for the client/server protocol.
-- Pure Lua (5.1+), no dependencies.  Conventions:
--   * arrays  = Lua tables with 1..n integer keys
--   * objects = everything else (an empty table encodes as {} and
--               decodes to an empty table — both consumers treat it as
--               an empty list, which is all the protocol needs)
--   * null    -> json.null sentinel (so a present-but-null field is
--               distinguishable from a missing one)
local json = {}

json.null = setmetatable({}, {__tostring = function() return "null" end})

local escapes = {
    ['"'] = '\\"', ['\\'] = '\\\\', ['\b'] = '\\b', ['\f'] = '\\f',
    ['\n'] = '\\n', ['\r'] = '\\r', ['\t'] = '\\t',
}

local function is_array(t)
    -- a table is an array when 1..#t are its only keys
    local n = #t
    local c = 0
    for _ in pairs(t) do
        c = c + 1
        if c > n then return false end
    end
    return c == n
end

local enc_value

local function enc_str(s)
    return '"' .. s:gsub('[%z\1-\31\\"]', function(c)
        return escapes[c] or string.format('\\u%04x', c:byte())
    end) .. '"'
end

local function enc_table(t, out)
    if is_array(t) then
        out[#out + 1] = "["
        for i = 1, #t do
            if i > 1 then out[#out + 1] = "," end
            enc_value(t[i], out)
        end
        out[#out + 1] = "]"
    else
        out[#out + 1] = "{"
        local first = true
        for k, v in pairs(t) do
            if not first then out[#out + 1] = "," end
            first = false
            out[#out + 1] = enc_str(tostring(k))
            out[#out + 1] = ":"
            enc_value(v, out)
        end
        out[#out + 1] = "}"
    end
end

enc_value = function(v, out)
    local ty = type(v)
    if v == json.null then out[#out + 1] = "null"
    elseif ty == "string" then out[#out + 1] = enc_str(v)
    elseif ty == "number" then out[#out + 1] = tostring(v)
    elseif ty == "boolean" then out[#out + 1] = tostring(v)
    elseif ty == "table" then enc_table(v, out)
    else out[#out + 1] = "null" end
end

function json.encode(v)
    local out = {}
    enc_value(v, out)
    return table.concat(out)
end

-- ------------------------------------------------------------ decode

local function decode_error(s, pos, msg)
    error("json: " .. msg .. " at byte " .. pos, 0)
end

local parse_value

local function skip_ws(s, pos)
    local _, e = s:find("^[ \t\r\n]*", pos)
    return e + 1
end

local function parse_str(s, pos)
    -- pos is at the opening quote
    local buf = {}
    local i = pos + 1
    while true do
        local c = s:sub(i, i)
        if c == "" then decode_error(s, i, "unterminated string") end
        if c == '"' then
            return table.concat(buf), i + 1
        elseif c == "\\" then
            local e = s:sub(i + 1, i + 1)
            if e == "u" then
                local hex = s:sub(i + 2, i + 5)
                local cp = tonumber(hex, 16)
                if not cp then decode_error(s, i, "bad \\u escape") end
                if cp < 128 then
                    buf[#buf + 1] = string.char(cp)
                elseif cp < 2048 then
                    buf[#buf + 1] = string.char(192 + math.floor(cp / 64),
                                                128 + cp % 64)
                else
                    buf[#buf + 1] = string.char(224 + math.floor(cp / 4096),
                                                128 + math.floor(cp / 64) % 64,
                                                128 + cp % 64)
                end
                i = i + 6
            else
                local map = {['"'] = '"', ['\\'] = '\\', ['/'] = '/',
                             b = '\b', f = '\f', n = '\n', r = '\r', t = '\t'}
                buf[#buf + 1] = map[e] or e
                i = i + 2
            end
        else
            buf[#buf + 1] = c
            i = i + 1
        end
    end
end

local function parse_arr(s, pos)
    local t = {}
    pos = skip_ws(s, pos + 1)
    if s:sub(pos, pos) == "]" then return t, pos + 1 end
    while true do
        local v
        v, pos = parse_value(s, pos)
        t[#t + 1] = v
        pos = skip_ws(s, pos)
        local c = s:sub(pos, pos)
        if c == "," then pos = skip_ws(s, pos + 1)
        elseif c == "]" then return t, pos + 1
        else decode_error(s, pos, "expected ',' or ']'") end
    end
end

local function parse_obj(s, pos)
    local t = {}
    pos = skip_ws(s, pos + 1)
    if s:sub(pos, pos) == "}" then return t, pos + 1 end
    while true do
        pos = skip_ws(s, pos)
        if s:sub(pos, pos) ~= '"' then
            decode_error(s, pos, "expected string key")
        end
        local k
        k, pos = parse_str(s, pos)
        pos = skip_ws(s, pos)
        if s:sub(pos, pos) ~= ":" then
            decode_error(s, pos, "expected ':'")
        end
        local v
        v, pos = parse_value(s, skip_ws(s, pos + 1))
        t[k] = v
        pos = skip_ws(s, pos)
        local c = s:sub(pos, pos)
        if c == "," then pos = pos + 1
        elseif c == "}" then return t, pos + 1
        else decode_error(s, pos, "expected ',' or '}'") end
    end
end

parse_value = function(s, pos)
    pos = skip_ws(s, pos)
    local c = s:sub(pos, pos)
    if c == '"' then return parse_str(s, pos)
    elseif c == "{" then return parse_obj(s, pos)
    elseif c == "[" then return parse_arr(s, pos)
    elseif c == "t" and s:sub(pos, pos + 3) == "true" then return true, pos + 4
    elseif c == "f" and s:sub(pos, pos + 4) == "false" then return false, pos + 5
    elseif c == "n" and s:sub(pos, pos + 3) == "null" then return json.null, pos + 4
    else
        local num = s:match("^-?%d+%.?%d*[eE]?[%+%-]?%d*", pos)
        if num and #num > 0 then
            return tonumber(num), pos + #num
        end
        decode_error(s, pos, "unexpected character '" .. c .. "'")
    end
end

function json.decode(s)
    local v, pos = parse_value(s, 1)
    pos = skip_ws(s, pos)
    if pos <= #s then decode_error(s, pos, "trailing data") end
    return v
end

return json
