---
---

-- cf. 3.3. Independencies in Graphs, p. 75

local util = require "lib.util"
local compute_graphs = require "model_checker.compute_graphs"

local function find_ancestors(backward_graph, given)
    local todo = util.shallow_copy(given)
    local ancestors = {}
    while util.count_entries(todo) ~= 0 do
        local current_node = next(todo)
        todo[current_node] = nil
        if not ancestors[current_node] then
            for ancestor,_ in pairs(backward_graph[current_node]) do
                todo[ancestor] = true
            end
        end
        ancestors[current_node] = true
    end
    return ancestors
end

local up = "↑"
local down = "↓"

local function make_entry_key(variable, up_down)
    local key = ("(%s,%s)"):format(variable, up_down)
    return key
end

local function make_entry_value(variable, up_down)
    local value = {variable=variable, up_down=up_down}
    return value
end

local function traverse_active_trails(forward_graph, backward_graph, start, given, ancestors)
    local todo = {}
    todo[make_entry_key(start, up)] = make_entry_value(start, up)
    local visited = {}
    local reachable = {}
    while util.count_entries(todo) ~= 0 do
        local current_key, current_value = next(todo)
        todo[current_key] = nil
        if not visited[current_key] then
            if not given[current_value.variable] then
                reachable[current_value.variable] = true
            end
            visited[current_key] = true
            if current_value.up_down == up and not given[current_value.variable] then
                for key,_ in pairs(backward_graph[current_value.variable]) do
                    todo[make_entry_key(key, up)] = make_entry_value(key, up)
                end
                for key,_ in pairs(forward_graph[current_value.variable]) do
                    todo[make_entry_key(key, down)] = make_entry_value(key, down)
                end
            elseif current_value.up_down == down then
                if not given[current_value.variable] then
                    for key,_ in pairs(forward_graph[current_value.variable]) do
                        todo[make_entry_key(key, down)] = make_entry_value(key, down)
                    end
                end
                if ancestors[current_value.variable] then
                    for key,_ in pairs(backward_graph[current_value.variable]) do
                        todo[make_entry_key(key, up)] = make_entry_value(key, up)
                    end
                end
            end
        end
    end
    return reachable
end

local function dependence(model, from, given)
    local forward_graph, backward_graph = compute_graphs(model)
    local ancestors = find_ancestors(backward_graph, given)
    local reachable = traverse_active_trails(forward_graph, backward_graph, from, given, ancestors)
    return reachable
end

return dependence
