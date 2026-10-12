-- tree_graphviz.lua — optional Graphviz layout for formula trees.
--
-- This module is shared between LuaJIT (native/kiosk) and Lua 5.4 + luaffifb
-- (browser web worker).  It tries several Graphviz backends in order:
--
--   1. Web-worker JS bridge: js.global.graphviz_layout(dot) -> plain text.
--   2. LuaJIT/luaffifb FFI: call libgvc/libcgraph directly.
--   3. Subprocess fallback: `dot -Tplain`.
--
-- If none are available, it returns nil and the caller falls back to the
-- pure-Lua layered layout.

local tree_graphviz = {}

local SCALE = 96  -- plain output is in inches; scale to pixels at 96 dpi

local function split_lines(s)
    local lines = {}
    for ln in (s or ""):gmatch("[^\r\n]+") do
        table.insert(lines, ln)
    end
    return lines
end

local function parse_plain(plain)
    local lines = split_lines(plain)
    if #lines == 0 then return nil end
    local w_str, h_str = lines[1]:match("^graph%s+[%d%.-]+%s+([%d%.-]+)%s+([%d%.-]+)")
    if not w_str or not h_str then return nil, "plain graph header not found" end
    local w, h = tonumber(w_str), tonumber(h_str)
    if not w or not h or w <= 0 or h <= 0 then
        return nil, "invalid plain graph dimensions"
    end

    local node_map = {}
    local edge_list = {}
    for i = 2, #lines do
        local ln = lines[i]
        if ln == "stop" then break end
        local name, x, y, nw, nh =
            ln:match("^node%s+(%S+)%s+([%d%.-]+)%s+([%d%.-]+)%s+([%d%.-]+)%s+([%d%.-]+)")
        if name then
            local id = tonumber(name)
            if id then
                node_map[id] = {
                    x = tonumber(x) * SCALE,
                    y = (h - tonumber(y)) * SCALE,  -- flip y so root is at top
                    w = tonumber(nw) * SCALE,
                    h = tonumber(nh) * SCALE,
                }
            end
        else
            local tail, head, npts, rest =
                ln:match("^edge%s+(%S+)%s+(%S+)%s+(%d+)%s+(.*)$")
            if tail then
                local points = {}
                local p = 1
                for _ = 1, tonumber(npts) do
                    local px, py, nx =
                        rest:match("^%s*([%d%.-]+)%s+([%d%.-]+)()", p)
                    if not px then break end
                    points[#points + 1] = {
                        tonumber(px) * SCALE,
                        (h - tonumber(py)) * SCALE,
                    }
                    p = nx
                end
                edge_list[#edge_list + 1] = {
                    tonumber(tail) or tail, tonumber(head) or head,
                    points = points,
                }
            end
        end
    end
    return { w = w * SCALE, h = h * SCALE, nodes = node_map,
             edges = edge_list }
end

local function js_layout(dot, engine)
    local ok, js = pcall(require, "js")
    if not ok or not js or not js.global then return nil end
    local fn = js.global.graphviz_layout
    if not fn then return nil end
    local out = fn(dot, engine or "dot")
    if type(out) ~= "string" then return nil end
    return parse_plain(out)
end

local function ffi_layout(dot, engine)
    local ok, ffi = pcall(require, "ffi")
    if not ok or not ffi then return nil end
    engine = engine or "dot"

    -- macOS / Linux common install locations
    local function try_load(name)
        local ok, h = pcall(ffi.load, name)
        if ok then return h end
        for _, path in ipairs({
            "/opt/homebrew/lib/lib" .. name .. ".dylib",
            "/usr/local/lib/lib" .. name .. ".dylib",
            "/opt/homebrew/lib/lib" .. name .. ".so",
            "/usr/local/lib/lib" .. name .. ".so",
            "/usr/lib/lib" .. name .. ".so",
            "/usr/lib/x86_64-linux-gnu/lib" .. name .. ".so",
        }) do
            local ok2, h2 = pcall(ffi.load, path)
            if ok2 then return h2 end
        end
        return nil
    end

    local libgvc = try_load("gvc")
    local libcgraph = try_load("cgraph")
    if not libgvc or not libcgraph then return nil end

    ffi.cdef [[
        typedef struct GVC_s GVC_t;
        typedef struct Agraph_s Agraph_t;
        typedef struct Agnode_s Agnode_t;

        GVC_t *gvContext(void);
        Agraph_t *agmemread(const char *cp);
        int gvLayout(GVC_t *gvc, Agraph_t *g, const char *engine);
        int gvRenderData(GVC_t *gvc, Agraph_t *g, const char *format,
                         char **result, size_t *length);
        void gvFreeRenderData(char *data);
        int gvFreeLayout(GVC_t *gvc, Agraph_t *g);
        int agclose(Agraph_t *g);
        int gvFreeContext(GVC_t *gvc);
    ]]

    local gvc = libgvc.gvContext()
    if gvc == nil then return nil end

    local g = libcgraph.agmemread(dot)
    if g == nil then
        libgvc.gvFreeContext(gvc)
        return nil
    end

    if libgvc.gvLayout(gvc, g, engine) ~= 0 then
        libcgraph.agclose(g)
        libgvc.gvFreeContext(gvc)
        return nil
    end

    local res = ffi.new("char*[1]")
    local len = ffi.new("size_t[1]")
    if libgvc.gvRenderData(gvc, g, "plain", res, len) ~= 0 then
        libgvc.gvFreeLayout(gvc, g)
        libcgraph.agclose(g)
        libgvc.gvFreeContext(gvc)
        return nil
    end

    local plain = ffi.string(res[0], len[0])
    libgvc.gvFreeRenderData(res[0])
    libgvc.gvFreeLayout(gvc, g)
    libcgraph.agclose(g)
    libgvc.gvFreeContext(gvc)

    return parse_plain(plain)
end

local function dot_layout(dot, engine)
    local tmp = os.tmpname()
    local f = io.open(tmp, "w")
    if not f then return nil end
    f:write(dot)
    f:close()

    engine = engine or "dot"
    -- only known GraphViz engine names may reach the shell command
    if not engine:match("^%a+$") then return nil end
    local p = io.popen(engine .. " -Tplain " .. tmp .. " 2>/dev/null")
    local out = p and p:read("*a")
    if p then p:close() end
    os.remove(tmp)

    if not out or out == "" then return nil end
    return parse_plain(out)
end

function tree_graphviz.layout(dot, engine)
    if not dot or dot == "" then return nil end
    local ok, layout = pcall(js_layout, dot, engine)
    if ok and layout then return layout end
    ok, layout = pcall(ffi_layout, dot, engine)
    if ok and layout then return layout end
    ok, layout = pcall(dot_layout, dot, engine)
    if ok and layout then return layout end
    return nil
end

return tree_graphviz
