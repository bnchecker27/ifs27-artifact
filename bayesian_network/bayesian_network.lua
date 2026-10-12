---
---

local util = require "lib.util"

local function is_array(result)
    if type(result) ~= "table" then
        return false
    end
    local max_number = 0
    for k,v in pairs(result) do
        if type(k) ~= "number" then
            return false
        end
        if k > max_number then
            max_number = k
        end
    end
    if #result ~= max_number then
        return false
    end
    return true
end

local function is_valid_variable_name(variable)
    if type(variable) ~= "string" then
        return false
    end
    if #variable == 0 then
        return false
    end
    return true
end

-- an outcome is a non-empty string or a finite real number; numeric
-- outcomes make the variable real-valued ("numval" feature — model
-- validation rejects mixing both kinds inside one node)
local function is_value(value)
    if type(value) == "number" then
        return value == value and math.abs(value) ~= math.huge
    end
    if type(value) ~= "string" then
        return false
    end
    if #value == 0 then
        return false
    end
    return true
end

local function is_probability(probability)
    if type(probability) ~= "number" then
        return false
    end
    return true
end

local function remove_comma(result)
    if result[#result] == "," then
        result[#result] = nil
    end
end

local function get_or_make_table_entry(t, entry)
    assert(type(t) == "table", type(t))
    assert(entry)
    local result = t[entry]
    if not result then
        t[entry] = {}
        result = t[entry]
    end
    return result
end

local function make_row_string(row)
    local hash_string = {}
    for _,key in ipairs(util.keys_to_sorted(row)) do
        local value = row[key]
        table.insert(hash_string, key)
        table.insert(hash_string, "↦")
        table.insert(hash_string, value)
        table.insert(hash_string, ",")
    end
    remove_comma(hash_string)
    hash_string = table.concat(hash_string)
    return hash_string
end

local function make_map_table()
    local result = {}
    local meta = {}
    local storage_map = {}
    local string_to_map = {}
    function meta.__index(t, k)
        if type(k) == "table" then
            local hash_string = make_row_string(k)
            return storage_map[hash_string]
        end
        error()
    end
    function meta.__newindex(t, key, value)
        assert(type(key) == "table")
        local key = util.shallow_copy(key)
        local value = value
        if type(value) == "table" then
            value = util.shallow_copy(value)
        end
        local hash_string = make_row_string(key)
        local kv_meta = {}
        function kv_meta.__tostring(what)
            return make_row_string(what)
        end
        setmetatable(key, kv_meta)
        setmetatable(value, kv_meta)
        storage_map[hash_string] = value
        local old_key = string_to_map[hash_string]
        if old_key then
            rawset(t, old_key, nil)
        end
        rawset(t, key, value)
        string_to_map[hash_string] = key
    end
    setmetatable(result, meta)
    return result
end

local function make_bn()
    local bn = {}
    bn.variables = {}

    function bn:get_variables()
        return util.keys_to_sorted(self.variables)
    end

    function bn:set_values(name, values)
        assert(is_valid_variable_name(name))
        assert(is_array(values))
        for _,value in ipairs(values) do
            assert(is_value(value))
        end
        local variable = get_or_make_table_entry(self.variables, name)
        variable.values = {}
        for _,v in ipairs(values) do
            table.insert(variable.values, v)
        end
    end

    function bn:is_variable(name)
        return util.toboolean(self.variables[name])
    end

    function bn:get_values(name)
        assert(is_valid_variable_name(name))
        assert(self.variables[name], name)
        return self.variables[name].values
    end

    function bn:get_values_or_nil(name)
        assert(is_valid_variable_name(name))
        if not self.variables[name] then
            return nil
        end
        assert(self.variables[name], name)
        return self.variables[name].values
    end

    function bn:set_probabilies(variable, row, probabilities)
        assert(is_valid_variable_name(variable))
        if not probabilities then
            for k,v in pairs(row) do
                bn:set_probabilies(variable, k, v)
            end
            return
        end
        assert(type(row) == "table")
        for k,v in pairs(row) do
            assert(is_valid_variable_name(k))
            assert(is_value(v))
        end
        for k,v in pairs(probabilities) do
            assert(is_value(k))
            assert(is_probability(v))
        end

        local variable_map = get_or_make_table_entry(self.variables, variable)
        local variable_probabilities = variable_map.probabilities
        if not variable_probabilities then
            variable_probabilities = make_map_table()
            variable_map.probabilities = variable_probabilities
        end
        local row_probabilities = {}
        for k,v in pairs(probabilities) do
            row_probabilities[k] = v
        end
        variable_probabilities[row] = row_probabilities
    end

    function bn:get_probabilities(variable, row)
        assert(is_valid_variable_name(variable))
        assert(row == nil or type(row) == "table")
        if row then
            for k,v in pairs(row) do
                assert(is_valid_variable_name(k))
                assert(is_value(v))
            end
        end
        local variable = self.variables[variable]
        if not variable then
            return {}
        end
        local variable_probabilities = variable.probabilities
        if not variable_probabilities then
            return {}
        end
        if not row then
            return variable_probabilities
        end
        return variable_probabilities[row]
    end

    function bn:get_dependents(variable)
        assert(is_valid_variable_name(variable))
        local variable = self.variables[variable]
        if not variable then
            return {}
        end
        local variable_probabilities = variable.probabilities
        if not variable_probabilities then
            return {}
        end
        local dependents
        for k,_ in pairs(variable_probabilities) do
            dependents = k
            break
        end
        if not dependents then
            return {}
        end
        local result = {}
        for k,_ in pairs(dependents) do
            table.insert(result, k)
        end
        table.sort(result)
        return result
    end

    function bn:remove_variable(variable)
        self.variables[variable] = nil
    end

    local meta = {}
    function meta.__tostring(what)
        local bn_to_tuple = require "bn_to_tuple"
        return bn_to_tuple(what)
    end
    setmetatable(bn, meta)
    return bn
end

return make_bn
