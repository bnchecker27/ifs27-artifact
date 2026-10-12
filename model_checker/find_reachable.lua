---
---

local util = require "lib.util"

local function search_reachable(graph, start)
    if type(start) == "string" then
        start = {start}
    end
    local seen = util.list_to_set(start)
    local todo = util.shallow_copy(start)
    while #todo > 0 do
        local node = todo[#todo]
        todo[#todo] = nil
        for succ,_ in pairs(graph[node] or {}) do
            if not seen[succ] then
                seen[succ] = true
                table.insert(todo, succ)
            end
        end
    end
    return util.set_to_list(seen)
end

return search_reachable
