-- tree_layout.lua — render a BayesL formula AST as a tree.
--
-- This runs on the server (LuaJIT native and WASM worker) and returns a
-- small JSON-friendly layout that the client draws.  Node x/y are the
-- centre of the node in pixels.  The preferred layout is Graphviz via
-- logic.tree_graphviz; a pure-Lua layered layout is kept as fallback.

local tree = {}

local dist_family = require "logic.dist_family"

-- lowercase operator names of the named-distribution literals, for the
-- "builtin" node kind (their keyword spellings are the default_symbols)
local PDIST_OPS = {}
for _, kw in ipairs(dist_family.order or {}) do
    PDIST_OPS[kw:lower()] = true
end

-- layout constants (units are client pixels)
tree.NODE_MIN_W    = 28
tree.NODE_H        = 24
tree.NODE_X_GAP    = 16
tree.NODE_Y_GAP    = 24
tree.NODE_CHAR_W   = 9

local function node_label(ast)
    if not ast or type(ast) ~= "table" then
        return "?"
    end
    if ast.type == "identifier" then
        return tostring(ast.identifier or ast.get_identifier and ast:get_identifier() or "?")
    end
    if ast.type == "box" then
        return "□"
    end
    if ast.type == "value" then
        return tostring(ast.value or ast.get_value and ast:get_value() or "?")
    end
    if ast.type == "operator" then
        local op = ast.operator or (ast.get_operator and ast:get_operator())
        if not op then return "?" end
        if op.default_symbol then
            return tostring(op.default_symbol)
        end
        local name = op.name
        if name == "prob" then return "ℙ" end
        if name == "map" then return "MAP" end
        if name == "mpe" then return "MPE" end
        if name == "idp" then return "IDP" end
        if name == "infl" then return "INFL" end
        if name == "modify_probability" then return "[...]" end
        if name == "let" then return "LET" end
        if name == "binding" then return "=" end
        return tostring(name)
    end
    return "?"
end

local function node_kind(ast)
    if not ast or type(ast) ~= "table" then
        return "identifier"
    end
    if ast.type == "box" then
        return "box"
    end
    if ast.type == "identifier" then
        return "identifier"
    end
    if ast.type == "value" then
        local v = ast.value or (ast.get_value and ast:get_value())
        if type(v) == "number" then
            return "number"
        end
        return "identifier"
    end
    if ast.type == "operator" then
        local op = ast.operator or (ast.get_operator and ast:get_operator())
        if not op then return "operator" end
        local name = op.name
        if name == "prob" or name == "map" or name == "mpe" or
           name == "idp" or name == "infl" or
           name == "expect" or name == "variance" or name == "sd" or
           name == "dist" or name == "rename" or name == "mux" or
           PDIST_OPS[name] then
            return "builtin"
        end
        if name == "not" or name == "and" or name == "nand" or
           name == "or" or name == "nor" or name == "implication" or
           name == "biimplication" or name == "xor" or
           name == "modify_probability" or name == "let"
           or name == "binding" then
            return "keyword"
        end
        return "operator"
    end
    return "identifier"
end

-- the AST-level type of the node: "box", "identifier", "number" or the
-- operator name ("and", "prob", "map", ...).  The client uses this to
-- decide which node types may replace the node in its parent's slot.
local function node_ntype(ast)
    if not ast or type(ast) ~= "table" then
        return "identifier"
    end
    if ast.type == "box" then
        return "box"
    end
    if ast.type == "identifier" then
        return "identifier"
    end
    if ast.type == "value" then
        return "number"
    end
    if ast.type == "operator" then
        local op = ast.operator or (ast.get_operator and ast:get_operator())
        return (op and op.name) or "operator"
    end
    return "identifier"
end

local function node_range(ast)
    local pos = ast.positional or (ast.get_positional and ast:get_positional())
    if pos then
        return pos.from or 0, pos.to or 0
    end
    return 0, 0
end

local function ident_name(ast)
    return tostring(ast.identifier
                  or (ast.get_identifier and ast:get_identifier()) or "")
end

local function build_tree(ast, nodes, edges, parent_id, names, bound)
    local id = #nodes + 1
    local from, to = node_range(ast)
    local n = {
        id = id,
        label = node_label(ast),
        kind = node_kind(ast),
        ntype = node_ntype(ast),
        from = from,
        to = to,
        children = {},
    }
    nodes[id] = n
    -- enum literals read differently from variable names: a
    -- string-valued leaf always is one, and an identifier spelling an
    -- outcome name is one too — unless it is a model variable or a
    -- LET-bound name (variables win, like the formula editor's colours)
    if ast.type == "value" then
        local v = ast.value or (ast.get_value and ast:get_value())
        if type(v) == "string" then n.enum = true end
    elseif ast.type == "identifier" and names then
        local nm = ident_name(ast)
        if (not bound or not bound[nm])
           and names.vals[nm] and not names.vars[nm] then
            n.enum = true
        end
    end
    -- MAP keeps the number of leading query-variable children so the
    -- client can tell them apart from the optional trailing condition
    if ast.type == "operator" then
        local op = ast.operator or (ast.get_operator and ast:get_operator())
        if op and op.name == "map" and op.identifier_list then
            n.nvars = #op.identifier_list
        end
        -- modify_probability children are {inner, target, map entries…,
        -- condition entries…}: the counts let the client assign each
        -- entry its role (outcome=probability vs variable=value)
        if op and op.name == "modify_probability" then
            n.nmaps = op.prob_map_count or 0
            n.nconds = op.condition_count or 0
        end
    end
    if parent_id then
        table.insert(edges, {from = parent_id, to = id})
        table.insert(nodes[parent_id].children, id)
    end
    if ast.type == "operator" then
        local op = ast.operator or (ast.get_operator and ast:get_operator())
        -- a LET node's bindings scope its whole subtree: the names its
        -- "binding" children declare shadow outcome names below
        local sub_bound = bound
        if op and op.name == "let" then
            sub_bound = {}
            if bound then for k in pairs(bound) do sub_bound[k] = true end end
            local num = ast.get_num_children and ast:get_num_children()
                  or (ast.children and #ast.children or 0)
            for i = 1, num do
                local ch = ast.get_child and ast:get_child(i)
                           or ast.children[i]
                local cop = ch and ch.get_operator and ch:get_operator()
                if cop and cop.name == "binding" then
                    local nm = ch.get_child and ch:get_child(1)
                    if nm and nm:get_type() == "identifier" then
                        sub_bound[ident_name(nm)] = true
                    end
                end
            end
        end
        local num = ast.get_num_children and ast:get_num_children()
              or (ast.children and #ast.children or 0)
        for i = 1, num do
            local child = ast.get_child and ast:get_child(i) or ast.children[i]
            build_tree(child, nodes, edges, id, names, sub_bound)
        end
    end
    return id
end

local function layout_builtin(nodes, root_id)
    local next_x = 0
    local function walk(id, depth)
        local n = nodes[id]
        n.h = tree.NODE_H
        n.w = math.max(tree.NODE_MIN_W, #n.label * tree.NODE_CHAR_W + 10)
        -- n.y is the node centre; depth y is the row's top edge.
        local y = depth * (tree.NODE_H + tree.NODE_Y_GAP) + n.h / 2
        if #n.children == 0 then
            n.x = next_x + n.w / 2
            n.y = y
            next_x = next_x + n.w + tree.NODE_X_GAP
        else
            local first_x, last_x
            for i, child_id in ipairs(n.children) do
                walk(child_id, depth + 1)
                if i == 1 then first_x = nodes[child_id].x end
                last_x = nodes[child_id].x
            end
            n.x = (first_x + last_x) / 2
            n.y = y
        end
    end
    walk(root_id, 0)

    -- Normalise so the bounding box starts at (0, 0).  n.x/n.y are
    -- centres, so measure using half extents.
    local min_left   = math.huge
    local min_top    = math.huge
    local max_right  = -math.huge
    local max_bottom = -math.huge
    for _, n in ipairs(nodes) do
        local left   = n.x - n.w / 2
        local right  = n.x + n.w / 2
        local top    = n.y - n.h / 2
        local bottom = n.y + n.h / 2
        if left   < min_left   then min_left   = left   end
        if top    < min_top    then min_top    = top    end
        if right  > max_right  then max_right  = right  end
        if bottom > max_bottom then max_bottom = bottom end
    end
    for _, n in ipairs(nodes) do
        n.x = n.x - min_left
        n.y = n.y - min_top
    end
    return max_right - min_left, max_bottom - min_top
end

local function escape_dot(s)
    return (s:gsub('"', '\\"'))
end

function tree.to_dot(nodes, edges)
    local out = {}
    table.insert(out, "digraph G {\n")
    table.insert(out, "  rankdir=TB;\n")
    table.insert(out, "  node [shape=box];\n")
    for _, n in ipairs(nodes) do
        table.insert(out, string.format(
            '  %d [label="%s" comment="f%d_t%d"];\n',
            n.id, escape_dot(n.label), n.from, n.to))
    end
    for _, e in ipairs(edges) do
        table.insert(out, string.format("  %d -> %d;\n", e.from, e.to))
    end
    table.insert(out, "}\n")
    return table.concat(out)
end

function tree.layout(ast, names)
    local nodes = {}
    local edges = {}
    local root = build_tree(ast, nodes, edges, nil, names, nil)
    local w, h = layout_builtin(nodes, root)
    local dot = tree.to_dot(nodes, edges)

    local ok, gvl = pcall(require, "logic.tree_graphviz")
    if ok and gvl then
        local gvlayout = gvl.layout(dot)
        if gvlayout and gvlayout.nodes then
            for id, pos in pairs(gvlayout.nodes) do
                local n = nodes[id]
                if n then
                    n.x, n.y, n.w, n.h = pos.x, pos.y, pos.w, pos.h
                end
            end
            w, h = gvlayout.w, gvlayout.h
        end
    end

    local node_list = {}
    for i = 1, #nodes do
        node_list[i] = nodes[i]
    end
    return {
        nodes = node_list,
        edges = edges,
        dot = dot,
        w = w,
        h = h,
    }
end

return tree
