---
---

local ffi = require "ffi"
local util = require "lib.util"

-- Factor memory lives in a grow-only ffi arena (prob_tables), invisible to
-- collectgarbage; a runaway elimination dies by kernel OOM, not a Lua error.
-- Two caps raise a catchable {resource_limit=true} error instead, which the
-- dispatcher treats as "try a cheaper solver".  MAX_FACTOR_ENTRIES bounds one
-- factor's table — the solvers materialize a Lua combo list per factor, so
-- this cap also bounds the Lua-heap side (~4M combos ≈ few hundred MB), and
-- any single multiply stays in the seconds range.  MAX_ARENA_ENTRIES bounds
-- the cumulative arena (~512 MiB of doubles); the arena never shrinks, so
-- this is the real process footprint.
local MAX_FACTOR_ENTRIES = 2^22  -- 4.2M entries = 32 MiB per factor
local MAX_ARENA_ENTRIES = 2^26   -- 67M entries = 512 MiB total
local debug_mem = os.getenv("BAYESL_DEBUG_MEM") ~= nil
local last_debug_mark = 0

local function new_mutable_model(max_factor_entries)
    local result = {}
    -- Optional override so tests can trip the cap without big allocations.
    result.max_factor_entries = max_factor_entries or MAX_FACTOR_ENTRIES
    result.variables = util.new_vector("int", true)
    result.num_variable_values = util.new_vector("int", true)
    result.unused_variable_numbers = util.new_vector("int", true)
    result.prob_tables = util.new_vector("double", true)
    result.variables_prob_tables = util.new_vector("int", true)
    result.prob_table_count = 0
    
    -- Store offsets for each prob_table to avoid recomputing during access
    result.prob_table_offsets = util.new_vector("uint64_t", true)

    function result:variable_add(num_values)
        local result
        if self.unused_variable_numbers:empty() then
            result = self.variables:size()
        else
            result = self.unused_variable_numbers:pop_back()
        end
        self.num_variable_values:resize(math.max(self.num_variable_values:size(), result + 1))
        self.num_variable_values[result] = num_values
        self.variables:push_back(result)
        return result
    end

    function result:variable_remove(variable)
        for i = 0, self.variables:size() - 1 do
            if self.variables[i] == variable then
                self.variables[i] = self.variables:pop_back()
                self.unused_variable_numbers:push_back(variable)
                break
            end
        end
    end

    function result:variable_get_num_values(variable)
        return self.num_variable_values[variable]
    end

    function result:variable_set_prob_table(variable, prob_table)
        local var_vals = self:variable_get_num_values(variable)
        local prob_vals = self:prob_table_get_num_values(prob_table)
        assert(var_vals == prob_vals)
        self.variables_prob_tables:resize(self.variables:size())
        self.variables_prob_tables[variable] = prob_table
    end
    
    function result:variable_get_prob_table(variable)
        return self.variables_prob_tables[variable]
    end

    function result:prob_table_new(num_values, dependents)
        local num_dependents = dependents:size()
        local prob_table_id = self.prob_table_count
        local prob_tables = self.prob_tables
        local old_size = prob_tables:size()
        
        -- Calculate number of probability entries
        local num_entries = num_values
        for i = 0, num_dependents - 1 do
            num_entries = num_entries * self:variable_get_num_values(dependents[i])
        end
        
        -- Memory layout (using old alignment formula for backward compatibility):
        -- Header: 2 uint32_t = 8 bytes (1 uint64_t)
        -- Dependents: num_dependents uint32_t, aligned to 8 bytes using math.ceil(num_dependents / 2) uint64_t units
        -- Offsets: num_dependents uint32_t, aligned to 8 bytes using math.ceil(num_dependents / 2) uint64_t units
        -- Probability entries: num_entries uint64_t (8 bytes each)
        
        local dependents_size = math.ceil(num_dependents / 2)  -- in uint64_t units
        local offsets_size = math.ceil(num_dependents / 2)  -- in uint64_t units
        local entries_size = num_entries  -- in uint64_t units
        
        local size_prob_table = 1 + dependents_size + offsets_size + entries_size  -- in uint64_t units
        
        if num_entries > self.max_factor_entries or old_size + size_prob_table > MAX_ARENA_ENTRIES then
            error({key="resource_limit", resource_limit=true}, 0)
        end
        if debug_mem and old_size - last_debug_mark >= 33554432 then
            last_debug_mark = old_size
            io.stderr:write(("[mem] arena=%.0fMB lua_heap=%.0fMB factor_entries=%d deps=%d\n")
                :format(old_size * 8 / 1048576, collectgarbage("count") / 1024,
                        num_entries, num_dependents))
        end
        prob_tables:resize(old_size + size_prob_table)
        
        local data = prob_tables:data()
        data = data + old_size
        local data_u8 = ffi.cast("uint8_t *", data)
        
        -- Write header
        local data_header = ffi.cast("uint32_t *", data_u8)
        data_header[0] = num_values
        data_header[1] = num_dependents
        
        -- Write dependents (aligned to 8 bytes)
        local data_dependents = ffi.cast("uint32_t *", data_u8 + 8)
        for i = 0, num_dependents - 1 do
            data_dependents[i] = dependents[i]
        end
        
        -- Write offsets (aligned to 8 bytes)
        local data_offsets = ffi.cast("uint32_t *", data_u8 + 8 + dependents_size * 8)
        local offset = num_values
        for i = num_dependents - 1, 0, -1 do
            data_offsets[i] = offset
            offset = offset * self:variable_get_num_values(dependents[i])
        end
        
        -- Initialize probability entries as uint64_t (for backward compatibility)
        local data_entries = ffi.cast("uint64_t *", data_u8 + 8 + dependents_size * 8 + offsets_size * 8)
        for i = 0, num_entries - 1 do
            data_entries[i] = 0
        end
        
        -- Store offset for this prob_table
        self.prob_table_offsets:push_back(old_size)
        
        -- Increment prob_table counter
        self.prob_table_count = self.prob_table_count + 1
        
        return prob_table_id
    end
    
    -- Helper function to get offset for a prob_table (stored at creation time)
    function result:get_prob_table_offset(prob_table_number)
        if prob_table_number >= self.prob_table_offsets:size() then
            return 0
        end
        return self.prob_table_offsets[prob_table_number]
    end

    function result:prob_table_get_num_values(prob_table_number)
        local prob_tables = self.prob_tables
        local data = prob_tables:data()
        local offset = self:get_prob_table_offset(prob_table_number)
        data = data + offset
        data = ffi.cast("uint32_t *", data)
        return tonumber(data[0])
    end

    function result:prob_table_get_num_dependents(prob_table_number)
        local prob_tables = self.prob_tables
        local data = prob_tables:data()
        local offset = self:get_prob_table_offset(prob_table_number)
        data = data + offset
        data = ffi.cast("uint32_t *", data)
        return tonumber(data[1])
    end
    
    function result:prob_table_get_dependent(prob_table_number, index)
        local prob_tables = self.prob_tables
        local data = prob_tables:data()
        local offset = self:get_prob_table_offset(prob_table_number)
        data = data + offset
        local data_u8 = ffi.cast("uint8_t *", data)
        local data_dependents = ffi.cast("uint32_t *", data_u8 + 8)
        return tonumber(data_dependents[index])
    end

    function result:prob_table_set_prob_entry(prob_table_number, value_number, dependents_values, probability)
        local prob_tables = self.prob_tables
        local data = prob_tables:data()
        local offset = self:get_prob_table_offset(prob_table_number)
        data = data + offset
        local data_u8 = ffi.cast("uint8_t *", data)
        local num_dependents = self:prob_table_get_num_dependents(prob_table_number)
        
        -- Calculate alignment sizes (using old formula)
        local dependents_size = math.ceil(num_dependents / 2)  -- in uint64_t units
        local offsets_size = math.ceil(num_dependents / 2)  -- in uint64_t units
        
        local data_dependents = ffi.cast("uint32_t *", data_u8 + 8)
        local data_offsets = ffi.cast("uint32_t *", data_u8 + 8 + dependents_size * 8)
        local index = value_number
        
        -- Use offsets array for reverse order indexing (reverse iteration)
        for i = num_dependents - 1, 0, -1 do
            local dep_val = dependents_values[i] or 0
            index = index + dep_val * data_offsets[i]
        end
        
        local data_entries = ffi.cast("double *", data_u8 + 8 + dependents_size * 8 + offsets_size * 8)
        data_entries[index] = probability
    end

    function result:prob_table_get_prob_entry(prob_table_number, value_number, dependents_values)
        local prob_tables = self.prob_tables
        local data = prob_tables:data()
        local offset = self:get_prob_table_offset(prob_table_number)
        data = data + offset
        local data_u8 = ffi.cast("uint8_t *", data)
        local num_dependents = self:prob_table_get_num_dependents(prob_table_number)
        
        -- Calculate alignment sizes (using old formula)
        local dependents_size = math.ceil(num_dependents / 2)  -- in uint64_t units
        local offsets_size = math.ceil(num_dependents / 2)  -- in uint64_t units
        
        local data_dependents = ffi.cast("uint32_t *", data_u8 + 8)
        local data_offsets = ffi.cast("uint32_t *", data_u8 + 8 + dependents_size * 8)
        local index = value_number
        
        -- Use offsets array for reverse order indexing (reverse iteration)
        for i = num_dependents - 1, 0, -1 do
            local dep_val = dependents_values[i] or 0
            index = index + dep_val * data_offsets[i]
        end
        
        local data_entries = ffi.cast("double *", data_u8 + 8 + dependents_size * 8 + offsets_size * 8)
        local value = tonumber(data_entries[index])
        
        return value
    end

    return result
end

return new_mutable_model
