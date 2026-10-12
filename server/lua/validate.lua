-- validate.lua — model validation for the RPM server.
--
-- Checks a client-supplied Bayesian-network model and returns ALL
-- problems found (the BIF parser stops at the first error; here the
-- client wants to mark every problem at once).
--
-- Model shape:
--   { nodes = {{id, name, desc, x, y, color?, outcomes = {str...},
--               cpt = {{p...}, ...}}, ...},     -- rows x outcome columns
--     edges = {{from, to}, ...} }              -- node ids
-- `color` is an optional "#rrggbb" canvas fill (win95 carries the
-- Norsys figure's category colours); validation ignores it.
--
-- Problem shape:
--   { sev = "error"|"warning", key, node?, row?, col?, cell?, msg }
-- `node` is a node id; `cell` is the flat 1-based CPT cell index
-- (row * outcomes + col) so the client can mark the exact cell.
--
-- Returns the problems array.  Pure Lua (5.1+/LuaJIT): used both by the
-- native LuaJIT server and by the web-worker's embedded Lua runtime.

local TOL = 1e-6

local function as_id(v)
    local n = tonumber(v)
    return n
end

local function validate_model(model, feature_set)
    local problems = {}
    -- "numval": real-valued outcomes are allowed; a node is numeric iff
    -- every outcome is a finite real number — a numeric string ("0.5")
    -- stays a plain string outcome.  Mixing numeric and non-numeric
    -- outcomes in one node is an error, as are numeric duplicates.
    -- Without the feature outcomes stay strings.
    local numval = feature_set and feature_set.numval
    local function err(key, msg, extra)
        local p = {sev = "error", key = key, msg = msg}
        if extra then for k, v in pairs(extra) do p[k] = v end end
        problems[#problems + 1] = p
    end
    local function warn(key, msg, extra)
        local p = {sev = "warning", key = key, msg = msg}
        if extra then for k, v in pairs(extra) do p[k] = v end end
        problems[#problems + 1] = p
    end

    if type(model) ~= "table" then
        err("no_model", "no model received")
        return problems
    end
    local nodes = type(model.nodes) == "table" and model.nodes or {}
    local edges = type(model.edges) == "table" and model.edges or {}

    local byId = {}
    for _, n in ipairs(nodes) do
        local id = type(n) == "table" and as_id(n.id) or nil
        if id and byId[id] == nil then byId[id] = n end
    end

    -- node names and outcome labels
    local nameSeen = {}
    for _, n in ipairs(nodes) do
        local id = as_id(n.id)
        local name = type(n.name) == "string" and n.name:gsub("%s+$", "") or ""
        if name == "" then
            err("empty_name", "a node has no name", {node = id})
        elseif nameSeen[name] then
            err("duplicate_name",
                string.format('duplicate node name "%s"', name), {node = id})
            err("duplicate_name",
                string.format('duplicate node name "%s"', name),
                {node = nameSeen[name]})
        else
            nameSeen[name] = id
        end

        local outs = type(n.outcomes) == "table" and n.outcomes or {}
        if #outs == 0 then
            err("no_outcomes",
                string.format('node "%s" has no outcome values', name),
                {node = id})
        end
        local vseen = {}
        local nseen = {}
        local n_numeric = 0
        local n_other = 0
        for _, v in ipairs(outs) do
            local sv = tostring(v)
            if vseen[sv] then
                err("duplicate_value",
                    string.format('node "%s" has duplicate outcome "%s"',
                                  name, sv), {node = id})
            end
            vseen[sv] = true
            local isnum = type(v) == "number"
            if isnum then
                local nv = v
                if not numval then
                    err("outcome_not_string",
                        string.format('node "%s": outcome %s is a number, '
                                      .. 'not a string', name, sv),
                        {node = id})
                end
                if nv ~= nv or math.abs(nv) == math.huge then
                    err("nonfinite_outcome",
                        string.format('node "%s": outcome "%s" is not a '
                                      .. 'finite real number', name, sv),
                        {node = id})
                elseif numval then
                    if nseen[nv] then
                        err("duplicate_value",
                            string.format('node "%s" has duplicate numeric '
                                          .. 'outcome "%s"', name, sv),
                            {node = id})
                    end
                    nseen[nv] = true
                end
                n_numeric = n_numeric + 1
            elseif type(v) ~= "string" and type(v) ~= "number" then
                err("outcome_not_string",
                    string.format('node "%s": outcome "%s" is not a string',
                                  name, sv), {node = id})
                n_other = n_other + 1
            else
                n_other = n_other + 1
            end
        end
        if numval and n_numeric > 0 and n_other > 0 then
            err("mixed_outcomes",
                string.format('node "%s" mixes real-valued and string '
                              .. 'outcomes', name), {node = id})
        end
    end

    -- edges: parent map + integrity
    local parents = {}   -- child id -> {parent id,...}
    for _, e in ipairs(edges) do
        local from = as_id(type(e) == "table" and e.from or nil)
        local to = as_id(type(e) == "table" and e.to or nil)
        if from == to then
            err("self_loop",
                string.format("node %s has an edge to itself",
                              tostring(from)), {node = from})
        end
        if not (from and byId[from]) or not (to and byId[to]) then
            err("dangling_edge",
                string.format("edge %s -> %s references an unknown node",
                              tostring(from), tostring(to)),
                {node = (from and byId[from]) and from or to})
        else
            parents[to] = parents[to] or {}
            local l = parents[to]
            l[#l + 1] = from
        end
    end

    -- directed cycles (DFS colouring)
    do
        local adj = {}
        for _, e in ipairs(edges) do
            local from, to = as_id(e.from), as_id(e.to)
            if from and to then
                adj[from] = adj[from] or {}
                local l = adj[from]
                l[#l + 1] = to
            end
        end
        local state = {}     -- nil unseen, 1 in stack, 2 done
        local inCycle = {}
        local stack = {}
        local dfs
        dfs = function(u)
            state[u] = 1
            stack[#stack + 1] = u
            for _, v in ipairs(adj[u] or {}) do
                if state[v] == 1 then
                    local seen = false
                    for _, w in ipairs(stack) do
                        if w == v then seen = true end
                        if seen then inCycle[w] = true end
                    end
                elseif not state[v] then
                    dfs(v)
                end
            end
            stack[#stack] = nil
            state[u] = 2
        end
        for _, n in ipairs(nodes) do
            local u = as_id(n.id)
            if u and not state[u] then dfs(u) end
        end
        for u in pairs(inCycle) do
            err("cycle",
                string.format("node %s is part of a directed cycle",
                              tostring(u)), {node = u})
        end
    end

    -- CPTs
    for _, n in ipairs(nodes) do
        local id = as_id(n.id)
        local name = tostring(n.name or "")
        local outs = type(n.outcomes) == "table" and n.outcomes or {}
        local nv = #outs
        local plist = parents[id] or {}
        local expected = 1
        for _, p in ipairs(plist) do
            local pn = byId[p]
            local k = pn and type(pn.outcomes) == "table"
                      and #pn.outcomes or 1
            expected = expected * math.max(1, k)
        end
        local cpt = type(n.cpt) == "table" and n.cpt or {}
        if #cpt == 0 then
            err("missing_cpt",
                string.format('node "%s" has no probability table', name),
                {node = id})
        else
            if #cpt ~= expected then
                err("cpt_row_count",
                    string.format('node "%s": CPT has %d rows, expected ' ..
                                  '%d (product of parent outcomes)',
                                  name, #cpt, expected), {node = id})
            end
            for r = 1, #cpt do
                local row = cpt[r]
                if type(row) ~= "table" then
                    err("cpt_row_width",
                        string.format('node "%s" row %d is not a list',
                                      name, r), {node = id, row = r})
                else
                    if #row ~= nv then
                        err("cpt_row_width",
                            string.format('node "%s" row %d has %d ' ..
                                          'entries, expected %d',
                                          name, r, #row, nv),
                            {node = id, row = r})
                    end
                    local sum = 0
                    local allNum = true
                    for c = 1, #row do
                        local v = row[c]
                        local cell = (r - 1) * nv + c
                        local num = tonumber(v)
                        if num == nil then
                            -- symbolic values (fractions, polynomials)
                            -- are allowed — they just cannot be checked
                            warn("cell_not_numeric",
                                 string.format('node "%s" row %d col %d: ' ..
                                               '"%s" is not a number — ' ..
                                               'cannot verify',
                                               name, r, c, tostring(v)),
                                 {node = id, row = r, col = c, cell = cell})
                            allNum = false
                        else
                            if num < 0 or num > 1 then
                                err("cell_out_of_range",
                                    string.format('node "%s" row %d col ' ..
                                                  '%d: %s outside [0,1]',
                                                  name, r, c, tostring(num)),
                                    {node = id, row = r, col = c, cell = cell})
                            end
                            sum = sum + num
                        end
                    end
                    if allNum and #row == nv and math.abs(sum - 1) > TOL then
                        err("row_sum",
                            string.format('node "%s" row %d probabilities ' ..
                                          'sum to %.6g, not 1',
                                          name, r, sum), {node = id, row = r})
                    end
                end
            end
        end
    end

    return problems
end

return validate_model
