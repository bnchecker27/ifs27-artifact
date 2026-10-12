local function bn_to_model(bn, options)
    options = options or {}
    local names = bn:get_variables()
    local by_name = {}
    for i, name in ipairs(names) do
        by_name[name] = { id = i, name = name, parents = {} }
    end

    local children = {}
    for i, name in ipairs(names) do
        local parents = bn:get_dependents(name)
        for _, p in ipairs(parents) do
            table.insert(by_name[name].parents, by_name[p].id)
            children[p] = children[p] or {}
            table.insert(children[p], name)
        end
    end

    local levels = {}
    local in_deg = {}
    for _, name in ipairs(names) do in_deg[name] = #by_name[name].parents end
    local queue = {}
    for _, name in ipairs(names) do
        if in_deg[name] == 0 then
            table.insert(queue, name)
            levels[name] = 0
        end
    end
    local head = 1
    while head <= #queue do
        local name = queue[head]; head = head + 1
        for _, c in ipairs(children[name] or {}) do
            in_deg[c] = in_deg[c] - 1
            if in_deg[c] == 0 then
                levels[c] = levels[name] + 1
                table.insert(queue, c)
            end
        end
    end

    local level_names = {}
    for _, name in ipairs(names) do
        local lv = levels[name] or 0
        level_names[lv] = level_names[lv] or {}
        table.insert(level_names[lv], name)
    end
    local x_spacing = options.x_spacing or 140
    local y_spacing = options.y_spacing or 110
    local margin = options.margin or 60
    local pos = {}
    for lv, lnames in pairs(level_names) do
        table.sort(lnames)
        for i, name in ipairs(lnames) do
            pos[name] = {
                x = margin + (i - 1) * x_spacing,
                y = margin + lv * y_spacing,
            }
        end
    end

    local nodes = {}
    for i, name in ipairs(names) do
        local outcomes = bn:get_values(name)
        local parents = bn:get_dependents(name)
        local np = #parents
        local nrows = 1
        for _, p in ipairs(parents) do
            nrows = nrows * #bn:get_values(p)
        end
        local cpt = {}
        if nrows > 0 then
            local strides = {}
            local stride = 1
            for p = np, 1, -1 do
                strides[p] = stride
                stride = stride * #bn:get_values(parents[p])
            end
            for r = 0, nrows - 1 do
                local cond = {}
                for p = 1, np do
                    local pname = parents[p]
                    local poutcomes = bn:get_values(pname)
                    local idx = math.floor(r / strides[p]) % #poutcomes
                    cond[pname] = poutcomes[idx + 1]
                end
                local probs = bn:get_probabilities(name, cond)
                local row = {}
                for c = 1, #outcomes do
                    row[c] = probs and probs[outcomes[c]] or 0
                end
                cpt[r + 1] = row
            end
        end
        nodes[i] = {
            id = i, name = name, desc = "",
            x = pos[name].x, y = pos[name].y,
            outcomes = outcomes, cpt = cpt,
        }
    end

    local edges = {}
    for _, name in ipairs(names) do
        for _, pname in ipairs(bn:get_dependents(name)) do
            table.insert(edges, {from = by_name[pname].id, to = by_name[name].id})
        end
    end

    return { nodes = nodes, edges = edges }
end

return bn_to_model
