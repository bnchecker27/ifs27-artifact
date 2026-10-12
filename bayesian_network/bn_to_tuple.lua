---
---

local function insert(result, ...)
    local arg = {...}
    for _,v in ipairs(arg) do
        table.insert(result, tostring(v))
    end
end

local function remove_comma(result)
    if result[#result] == "," then
        result[#result] = nil
    end
end

local function to_string_values(bn, result)
    insert(result, "{")
    for _,variable in ipairs(bn:get_variables()) do
        insert(result, variable, "↦{")
        for _,value in ipairs(bn:get_values(variable)) do
            insert(result, value, ",")
        end
        remove_comma(result)
        insert(result, "}", ",")
    end
    remove_comma(result)
    insert(result,"}")
end

local function to_string_probabilities(bn, result)
    table.insert(result, "{")
    for _,variable in ipairs(bn:get_variables()) do
        local variable_probabilities = bn:get_probabilities(variable)
        insert(result, variable, "↦", "{")
        for row, values in pairs(variable_probabilities) do
            insert(result, "{", row, "}↦{", values, "}", ",")
        end
        remove_comma(result)
        insert(result, "}", ",")
    end
    remove_comma(result)
    table.insert(result,"}")
end

local function to_string(bn)
    assert(bn)
    local result = {}
    insert(result, "(")
    to_string_values(bn, result)
    insert(result,",")
    to_string_probabilities(bn, result)
    insert(result,")")
    return table.concat(result)
end

return to_string
