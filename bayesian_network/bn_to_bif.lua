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
    elseif result[#result] == " " and result[#result - 1] == "," then
        result[#result] = nil
        result[#result] = nil
    end
end

local function to_string_values(bn, result)
    for _,variable in ipairs(bn:get_variables()) do
        local values = bn:get_values(variable)
        insert(result, "variable ", variable, " {\n")
        insert(result, "  type discrete [ ", #values, " ] { ")
        for _,value in ipairs(values) do
            insert(result, value, ",", " ")
        end
        remove_comma(result)
        insert(result, " };\n", "}\n")
    end
end

local function to_string_probabilities(bn, result)
    for _,variable in ipairs(bn:get_variables()) do
        local variable_probabilities = bn:get_probabilities(variable)
        local dependents = bn:get_dependents(variable)
        local values = bn:get_values(variable)
        if #dependents == 0 then
            local probabilities = variable_probabilities[{}]
            insert(result, "probability ( ", variable, " ) {\n")
            insert(result, "  table ")
            for _,variable in ipairs(values) do
                insert(result, probabilities[variable], ",", " ")
            end
            remove_comma(result)
            insert(result, ";\n}\n")
        else
            local dependents = bn:get_dependents(variable)
            insert(result, "probability ( ", variable, " | ")
            for _,dependent in ipairs(dependents) do
                insert(result, dependent, ",", " ")
            end
            remove_comma(result)
            insert(result, " ) {\n")
            for map, distr in pairs(variable_probabilities) do
                insert(result, "  (")
                for _,dependent in ipairs(dependents) do
                    insert(result, map[dependent], ",", " ")
                end
                remove_comma(result)
                insert(result, ") ")
                for _,variable in ipairs(values) do
                    insert(result, distr[variable], ",", " ")
                end
                remove_comma(result)
                insert(result, ";\n")
            end
            insert(result, "}\n")
        end
    end
end

local function to_string(bn)
    assert(bn)
    local result = {}
    insert(result, "network unknown {\n}\n")
    to_string_values(bn, result)
    to_string_probabilities(bn, result)
    return table.concat(result)
end

return to_string
