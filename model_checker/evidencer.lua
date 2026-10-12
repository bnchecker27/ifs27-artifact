---
---

-- TODO find less stupid name for this file

local make_sampler = require "model_checker.sampler_auto"
local util = require "lib.util"
local ffi = require "ffi"

local function compute_result_assignment(model, entries, identifier_list)
    local meta = {}
    function meta.__tostring(t)
        local order = {}
        for k,_ in pairs(t) do
            table.insert(order, k)
        end
        table.sort(order)
        local result = {}
        table.insert(result, "{")
        for _,k in ipairs(order) do
            local v = t[k]
            table.insert(result, k)
            table.insert(result, "↦")
            table.insert(result, v)
            table.insert(result, ",")
        end
        if result[#result] == "," then
            result[#result] = nil
        end
        table.insert(result, "}")
        return table.concat(result)
    end
    local argmax
    local max = 0

    for k,v in pairs(entries) do
        if v > max then
            max = v
            argmax = k
        end
    end
    
    -- Handle case where no samples matched the condition
    if not argmax then
        return {}
    end
    
    local result = {}
    for number,identifier in ipairs(identifier_list) do
        local value_number = argmax:byte(number)
        local value = model:get_values(identifier)[value_number + 1]
        result[identifier] = value
    end
    setmetatable(result, meta)
    return result
end

local function evidence_solver(model, cond, identifier_list, options)
    local sampler = make_sampler(model, options)
    local buffer = ffi.new("char[?]", #identifier_list)
    local cond_number = cond and sampler:get_variable_to_number(cond) or nil
    local id_number_list = {}
    for _,identifier in ipairs(identifier_list) do
        local id = sampler:get_variable_to_number(identifier)
        table.insert(id_number_list, id)
    end
    local total = 0
    local entries = {}
    -- The entries table grows with the number of distinct assignments seen;
    -- bail out cleanly instead of letting the Lua heap die by OOM.
    local calls = 0
    local function callback(assignment, weight)
        calls = calls + 1
        if calls % 4096 == 0 and util.lua_heap_over(1536 * 1024) then
            error({key="resource_limit", resource_limit=true}, 0)
        end
        if cond_number == nil or assignment[cond_number] == 1 then
            for number,id in ipairs(id_number_list) do
                buffer[number-1] = assignment[id]
            end
            local buf_str = ffi.string(buffer, #id_number_list)
            entries[buf_str] = (entries[buf_str] or 0) + weight
            total = total + weight
        end
    end
    sampler:set_callback(callback)
    sampler:run()
    local result = compute_result_assignment(model, entries, identifier_list)
    return result
end

return evidence_solver
