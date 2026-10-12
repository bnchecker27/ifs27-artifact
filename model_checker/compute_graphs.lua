---
---


local function compute_graphs(model)
    local backward_graph, forward_graph = {}, {}
    for _,source_variable in ipairs(model:get_variables()) do
        backward_graph[source_variable] = {}
        for _,target_variable in ipairs(model:get_dependents(source_variable)) do
            backward_graph[source_variable][target_variable] = true
            if not forward_graph[target_variable] then
                forward_graph[target_variable] = {}
            end
            forward_graph[target_variable][source_variable] = true
        end
    end
    for _,source_variable in ipairs(model:get_variables()) do
        if not forward_graph[source_variable] then
            forward_graph[source_variable] = {}
        end
    end
    return forward_graph, backward_graph
end

return compute_graphs
