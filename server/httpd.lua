#!/usr/bin/env luajit
--[[
httpd.lua — standalone GUI host + RPC server in LuaJIT.

Serves the prebuilt browser GUI (index.html/index.js/index.wasm/…) as
static files and exposes the model-checker service over plain HTTP:
the browser GUI is only the client — every formula is parsed and
evaluated natively by LuaJIT here, never in the browser.

Protocol: the client speaks the service's 4-byte framed JSON over a
persistent link; over HTTP each request is simply one JSON document.

    GET  /health        -> "ok" (liveness probe for the JS client)
    GET  /              -> index.html (and any other static file)
    POST /rpc           -> body: one service JSON message;
                           reply: the service's JSON response

Usage:
    luajit server/httpd.lua [port]
        (default port 8082, env BAYESL_HTTP_PORT;
         bind address env BAYESL_BIND, default 127.0.0.1;
         static dir env BAYESL_WEB_DIR, default ./gui/web or
         ../nuklear-ime-demo/web relative to this script;
         model file env BAYESL_MODEL_FILE or model.json next to
         this script;
         default features env BAYESL_FEATURES — merged into requests
         that do not carry their own "features" field)
]]

local ffi = require "ffi"
local bit = require "bit"

ffi.cdef [[
    typedef long nkl_ssize_t;
    typedef unsigned int nkl_socklen_t;
    typedef void (*nkl_sighandler_t)(int);
    typedef struct { int32_t fds_bits[32]; } nkl_fd_set;
    struct nkl_timeval { long tv_sec; int tv_usec; };
    int socket(int domain, int type, int protocol);
    int bind(int sockfd, const void *addr, nkl_socklen_t addrlen);
    int listen(int sockfd, int backlog);
    int accept(int sockfd, void *addr, void *addrlen);
    nkl_ssize_t recv(int sockfd, void *buf, unsigned long len, int flags);
    nkl_ssize_t send(int sockfd, const void *buf, unsigned long len,
                     int flags);
    int close(int fd);
    int setsockopt(int fd, int level, int optname, const void *optval,
                   nkl_socklen_t optlen);
    int select(int nfds, nkl_fd_set *rfds, nkl_fd_set *wfds,
               nkl_fd_set *efds, struct nkl_timeval *tv);
    nkl_sighandler_t signal(int signum, nkl_sighandler_t handler);
]]

local SIGPIPE = 13
ffi.C.signal(SIGPIPE, ffi.cast("nkl_sighandler_t", 1))

-- POSIX constants (macOS/Linux agree on these)
local AF_INET, SOCK_STREAM = 2, 1
local SOL_SOCKET, SO_REUSEADDR = 0xffff, 4

local dir = (arg and arg[0] and arg[0]:match("^(.*[/\\])")) or "./"
local PORT = tonumber(arg and arg[1])
             or tonumber(os.getenv("BAYESL_HTTP_PORT")) or 8082
local BIND = os.getenv("BAYESL_BIND") or "127.0.0.1"
local WEB_DIR = os.getenv("BAYESL_WEB_DIR")
local MODEL_FILE = os.getenv("BAYESL_MODEL_FILE") or (dir .. "model.json")
local DEFAULT_FEATURES = os.getenv("BAYESL_FEATURES")

if not WEB_DIR then
    -- artefact layout has gui/web next to server/; the repository has
    -- the emscripten output under nuklear-ime-demo/web
    for _, cand in ipairs({dir .. "../gui/web",
                           dir .. "../nuklear-ime-demo/web"}) do
        local f = io.open(cand .. "/index.html", "r")
        if f then f:close(); WEB_DIR = cand; break end
    end
    WEB_DIR = WEB_DIR or (dir .. "../gui/web")
end

-- Make repo-root and bundled build dependencies reachable to `require`.
package.path = dir .. "../?.lua;" .. dir .. "../?/init.lua;" .. package.path
package.cpath = dir .. "../build/lpeg-1.1.0/?.so;" .. package.cpath

local function readfile(p, mode)
    local f = io.open(p, mode or "r")
    if not f then return nil end
    local s = f:read("*a")
    f:close()
    return s
end

-- the service core gets its dependencies as source strings so the same
-- chunk also runs inside the web worker (which has no filesystem);
-- json.lua may be bundled under lua/ (artefact) or in the shared
-- nuklear-ime-demo directory (repository)
local service_src = assert(readfile(dir .. "lua/service.lua"))
local json_src = readfile(dir .. "lua/json.lua")
              or assert(readfile(dir .. "../nuklear-ime-demo/json.lua"))
local validate_src = assert(readfile(dir .. "lua/validate.lua"))
local dispatch = assert(load(service_src, "service.lua"))(
    json_src, validate_src)

-- JSON decode for feature injection — reuse the same codec the
-- service uses so the wire format round-trips identically.
local json = assert(load(json_src, "json.lua"))()

local hooks = {
    save = function(text)
        local f = assert(io.open(MODEL_FILE, "w"))
        f:write(text)
        f:close()
    end,
}

local function serve_request(raw)
    -- merge the server's default feature set into requests that do not
    -- specify one (the GUI sends FEATURE.set, which may be nil)
    if DEFAULT_FEATURES then
        local ok, msg = pcall(json.decode, raw)
        if ok and type(msg) == "table" and msg.features == nil then
            msg.features = DEFAULT_FEATURES
            raw = json.encode(msg)
        end
    end
    return dispatch(raw, hooks)
end

-- restore the stored model once at startup: wrap the file content in a
-- restore_model message — no decode needed, the service parses it
do
    local f = io.open(MODEL_FILE, "r")
    if f then
        local text = f:read("*a")
        f:close()
        if #text > 0 then
            dispatch('{"method":"restore_model","model":' .. text .. '}')
            print("model restored from " .. MODEL_FILE)
        end
    end
end

-- ---------------------------------------------------------------------
-- sockets

local listener = ffi.C.socket(AF_INET, SOCK_STREAM, 0)
assert(listener >= 0, "socket() failed")
local one = ffi.new("int[1]", 1)
ffi.C.setsockopt(listener, SOL_SOCKET, SO_REUSEADDR, one, 4)

local sa
if ffi.os == "Linux" then
    sa = ffi.new([[struct {
        uint16_t sin_family;
        uint16_t sin_port;
        uint32_t sin_addr;
        char     sin_zero[8];
    }]])
else
    sa = ffi.new([[struct {
        uint8_t  sin_len;
        uint8_t  sin_family;
        uint16_t sin_port;
        uint32_t sin_addr;
        char     sin_zero[8];
    }]])
    sa.sin_len = 16
end
sa.sin_family = AF_INET

local function parse_ipv4(s)
    local a, b, c, d = s:match("^(%d+)%.(%d+)%.(%d+)%.(%d+)$")
    assert(a, "invalid BAYESL_BIND address: " .. tostring(s))
    a, b, c, d = tonumber(a), tonumber(b), tonumber(c), tonumber(d)
    -- sockaddr_in.sin_addr is in network byte order
    return a + b * 256 + c * 65536 + d * 16777216
end

sa.sin_port = bit.bor(bit.lshift(bit.band(PORT, 0xff), 8),
                      bit.rshift(bit.band(PORT, 0xff00), 8))
sa.sin_addr = parse_ipv4(BIND)
assert(ffi.C.bind(listener, sa, ffi.sizeof(sa)) == 0,
       "bind " .. BIND .. ":" .. PORT .. " failed")
assert(ffi.C.listen(listener, 8) == 0, "listen failed")
print("bn gui server (luajit) listening on http://" .. BIND .. ":" .. PORT)
print("serving " .. WEB_DIR)

-- ---------------------------------------------------------------------
-- HTTP

local MIME = {
    html = "text/html; charset=utf-8",
    js   = "text/javascript; charset=utf-8",
    mjs  = "text/javascript; charset=utf-8",
    wasm = "application/wasm",
    data = "application/octet-stream",
    json = "application/json; charset=utf-8",
    css  = "text/css; charset=utf-8",
    png  = "image/png",
    jpg  = "image/jpeg",
    ico  = "image/x-icon",
    svg  = "image/svg+xml",
    txt  = "text/plain; charset=utf-8",
    map  = "application/json",
    ttf  = "font/ttf",
    otf  = "font/otf",
}

local function http_response(status, body, ctype, extra, head_only)
    local head = "HTTP/1.1 " .. status .. "\r\n"
        .. "Content-Length: " .. #body .. "\r\n"
        .. "Content-Type: " .. ctype .. "\r\n"
        .. "Connection: close\r\n"
        .. (extra or "")
        .. "\r\n"
    return head_only and head or (head .. body)
end

local function not_found()
    return http_response("404 Not Found", "not found", "text/plain")
end

local function serve_static(path)
    -- strip query and %-escapes, refuse path escapes
    path = path:gsub("%?.*$", ""):gsub("%%(%x%x)",
        function(h) return string.char(tonumber(h, 16)) end)
    if path == "/" or path == "" then path = "/index.html" end
    if path:find("%.%.") then return nil end
    local p = WEB_DIR .. path
    local f = io.open(p, "rb")
    if not f then return nil end
    local body = f:read("*a")
    f:close()
    local ext = p:match("%.([%w]+)$") or ""
    return body, MIME[ext] or "application/octet-stream"
end

local function handle_request(req)
    local method, path = req:match("^(%u+)%s+(%S+)%s+HTTP")
    if not method then return nil, nil end
    if method == "GET" or method == "HEAD" then
        if path == "/health" or path == "/rpc" then
            return http_response("200 OK", "ok", "text/plain")
        end
        local body, ctype = serve_static(path)
        if body then
            return http_response("200 OK", body, ctype, nil,
                                 method == "HEAD")
        end
        return not_found()
    elseif method == "POST" then
        if path:gsub("%?.*$", "") ~= "/rpc" then
            return http_response("405 Method Not Allowed",
                                 "POST only on /rpc", "text/plain")
        end
        -- the caller guarantees the buffered request is complete
        local he = req:find("\r\n\r\n", 1, true)
        local body = he and req:sub(he + 4) or ""
        local reply = serve_request(body)
        return http_response("200 OK", reply,
                             "application/json; charset=utf-8")
    end
    return http_response("405 Method Not Allowed", "method not allowed",
                         "text/plain")
end

-- request completeness: headers terminated, body matches
-- Content-Length (POST); GET/HEAD requests are bodiless here
local function request_complete(buf)
    local he = buf:find("\r\n\r\n", 1, true)
    if not he then return false end
    local method = buf:match("^(%u+)%s")
    if method == "POST" then
        -- header names are case-insensitive
        local len
        for line in buf:sub(1, he):gmatch("[^\r\n]+") do
            local v = line:match("^[Cc][Oo][Nn][Tt][Ee][Nn][Tt]%-[Ll][Ee][Nn][Gg][Tt][Hh]%s*:%s*(%d+)")
            if v then len = tonumber(v) end
        end
        if not len then return true end   -- no length -> empty body
        return #buf >= he + 3 + len
    end
    return true
end

local rbuf = ffi.new("char[65536]")
local rfds = ffi.new("nkl_fd_set")
local tv = ffi.new("struct nkl_timeval")

local function fd_zero(set)
    for i = 0, 31 do set.fds_bits[i] = 0 end
end
local function fd_set(set, fd)
    local i = math.floor(fd / 32)
    set.fds_bits[i] = bit.bor(set.fds_bits[i], bit.lshift(1, fd % 32))
end
local function fd_isset(set, fd)
    return bit.band(set.fds_bits[math.floor(fd / 32)],
                    bit.lshift(1, fd % 32)) ~= 0
end

local function send_all(fd, s)
    local buf = ffi.new("char[?]", #s)
    ffi.copy(buf, s, #s)
    local off = 0
    while off < #s do
        local n = tonumber(ffi.C.send(fd, buf + off, #s - off, 0))
        if n <= 0 then return false end
        off = off + n
    end
    return true
end

local clients = {}
local MAX_REQUEST = 64 * 1024 * 1024  -- models/formulas stay well below this

while true do
    fd_zero(rfds)
    local maxfd = listener
    fd_set(rfds, listener)
    for _, c in ipairs(clients) do
        fd_set(rfds, c.fd)
        if c.fd > maxfd then maxfd = c.fd end
    end
    tv.tv_sec = 0
    tv.tv_usec = 100000
    local n = tonumber(ffi.C.select(maxfd + 1, rfds, nil, nil, tv))
    if n and n > 0 then
        if fd_isset(rfds, listener) then
            local fd = tonumber(ffi.C.accept(listener, nil, nil))
            if fd and fd >= 0 then
                clients[#clients + 1] = {fd = fd, buf = ""}
            end
        end
        for i = #clients, 1, -1 do
            local c = clients[i]
            if fd_isset(rfds, c.fd) then
                local got = tonumber(ffi.C.recv(c.fd, rbuf, 65536, 0))
                if not got or got <= 0 then
                    ffi.C.close(c.fd)
                    table.remove(clients, i)
                else
                    c.buf = c.buf .. ffi.string(rbuf, got)
                    if #c.buf > MAX_REQUEST then
                        send_all(c.fd, http_response(
                            "413 Payload Too Large", "too large",
                            "text/plain"))
                        ffi.C.close(c.fd)
                        table.remove(clients, i)
                    elseif request_complete(c.buf) then
                        local resp = handle_request(c.buf)
                            or http_response("400 Bad Request", "bad request",
                                             "text/plain")
                        send_all(c.fd, resp)
                        ffi.C.close(c.fd)
                        table.remove(clients, i)
                    end
                end
            end
        end
    end
end
