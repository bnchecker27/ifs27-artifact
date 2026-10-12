---
---

local compute_graphs = require "model_checker.compute_graphs"

local function sorted_graph(graph)
    local result = {}
    for variable, successors in pairs(graph) do
        local sorted_successors = {}
        for successor, _ in pairs(successors) do
            table.insert(sorted_successors, successor)
        end
        table.sort(sorted_successors)
        result[variable] = sorted_successors
    end
    return result
end

local function toposort_variable(variable, graph, seen, order)
    if seen[variable] then
        return
    end
    local stack = {}
    local in_stack = {}
    table.insert(stack, {variable=variable, successor_index=1})
    assert(not in_stack[variable], {key="cycle_detected", parameters={variable=variable}})
    in_stack[variable] = true
    seen[variable] = true
    while #stack > 0 do
        local entry = stack[#stack]
        local variable = entry.variable
        local successor_index = entry.successor_index
        local successors = graph[variable]
        local successor = successors[successor_index]
        if not successor then
            table.insert(order, variable)
            stack[#stack] = nil
            in_stack[variable] = false
        else
            stack[#stack].successor_index = successor_index + 1
            entry = {variable=successor, successor_index=1}
            if not seen[entry.variable] then
                seen[entry.variable] = true
                table.insert(stack, entry)
                assert(not in_stack[entry.variable], {key="cycle_detected", parameters={variable=entry.variable}})
                in_stack[entry.variable] = true
            end
        end
    end
end


local function toposort(model)
    assert(model)
    local _, graph_ = compute_graphs(model)
    graph_ = sorted_graph(graph_)

    local seen = {}
    local order = {}
    for _,variable in ipairs(model:get_variables()) do
        toposort_variable(variable, graph_, seen, order)
    end
    return order
end

return toposort
