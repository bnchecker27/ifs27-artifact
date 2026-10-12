---
--- Variable elimination solver for MAP (Maximum A Posteriori) using max-product
---

local mutable_bn = require "model_checker.mutable_bn"
local util = require "lib.util"
local logic = require "logic.logic"
local operators = require "logic.operators"
local bindings = require "model_checker.bindings"
local boolean_claim = require "model_checker.boolean_claim"

-- Lua-heap ceiling: the ffi factor arena is metered inside mutable_bn, but
-- Lua-side structures can grow just as large; past this limit bail out with
-- a catchable resource_limit error so the dispatcher can fall back.
local LUA_HEAP_LIMIT_KB = 1536 * 1024

local op_and
for _,op in ipairs(operators.logical_operators) do
    if op.name == "and" then
        op_and = op
        break
    end
end

local op_equal
for _,op in ipairs(operators.compare_operators) do
    if op.name == "equal" then
        op_equal = op
        break
    end
end

local function make_map_property(result, positional)
    local vars = {}
    for var, _ in pairs(result) do
        table.insert(vars, var)
    end
    table.sort(vars)

    if #vars == 0 then
        return nil
    end

    local function make_eq(var, value)
        -- outcome nodes spell like the parser's own literals: numeric
        -- outcomes ("numval") are value nodes, string outcomes are
        -- identifiers — an identifier carrying a number is not a
        -- valid variable name downstream
        local rhs = type(value) == "number"
                and logic.make_value(value, positional)
                or  logic.make_identifier(tostring(value), positional)
        return logic.make_binary_operator(
                logic.make_identifier(var, positional),
                rhs,
                op_equal,
                positional)
    end

    local current = make_eq(vars[1], result[vars[1]])
    for i = 2, #vars do
        current = logic.make_binary_operator(
                current,
                make_eq(vars[i], result[vars[i]]),
                op_and,
                positional)
    end
    return current
end

local function convert_to_mutable_bn(original)
    local result = mutable_bn()
    local variable_name_to_id = {}
    local id_to_variable_name = {}
    local pt_to_dependents = {}
    local var_num_values = {}
    local var_value_names = {}
    
    for _,node in ipairs(original:get_variables()) do
        local values = original:get_values(node)
        local num_values = #values
        local var_id = result:variable_add(num_values)
        variable_name_to_id[node] = var_id
        id_to_variable_name[var_id] = node
        var_num_values[var_id] = num_values
        var_value_names[var_id] = values
    end
    
    for _,node in ipairs(original:get_variables()) do
        local var_id = variable_name_to_id[node]
        local dependents = original:get_dependents(node)
        local dependents_vector = util.new_vector("int", true)
        local dependents_ids = {}
        for _,dep in ipairs(dependents) do
            local dep_id = variable_name_to_id[dep]
            dependents_vector:push_back(dep_id)
            table.insert(dependents_ids, dep_id)
        end
        local num_values = result:variable_get_num_values(var_id)
        local pt = result:prob_table_new(num_values, dependents_vector)
        result:variable_set_prob_table(var_id, pt)
        result.variables_prob_tables[var_id] = pt
        pt_to_dependents[pt] = dependents_ids
        
        local probabilities = original:get_probabilities(node)
        if next(probabilities) then
            for row, probs in pairs(probabilities) do
                local deps_values_table = {}
                for i,dep in ipairs(dependents) do
                    local dep_value = row[dep]
                    local dep_values = original:get_values(dep)
                    local dep_index = 0
                    for j, v in ipairs(dep_values) do
                        if v == dep_value then
                            dep_index = j - 1
                            break
                        end
                    end
                    deps_values_table[i - 1] = dep_index
                end
                for val_name, prob in pairs(probs) do
                    local val_index = 0
                    local all_values = original:get_values(node)
                    for i, v in ipairs(all_values) do
                        if v == val_name then
                            val_index = i - 1
                            break
                        end
                    end
                    result:prob_table_set_prob_entry(pt, val_index, deps_values_table, prob)
                end
            end
        end
    end
    
    return result, variable_name_to_id, id_to_variable_name, pt_to_dependents, var_num_values, var_value_names
end

local function generate_combinations(variable_ids, var_num_values)
    -- Bail before materializing a combo list beyond the per-factor ceiling:
    -- the Lua heap would die before the arena cap in mutable_bn could trip.
    local total = 1
    for _, var_id in ipairs(variable_ids) do
        total = total * (var_num_values[var_id] or 2)
        if total > 2^22 then
            error({key="resource_limit", resource_limit=true}, 0)
        end
    end

    local combinations = {}
    local emitted = 0
    local function recurse(index, current)
        if index > #variable_ids then
            emitted = emitted + 1
            if emitted % 65536 == 0 and util.lua_heap_over(LUA_HEAP_LIMIT_KB) then
                error({key="resource_limit", resource_limit=true}, 0)
            end
            table.insert(combinations, util.shallow_copy(current))
            return
        end
        local var_id = variable_ids[index]
        local num_values = var_num_values[var_id] or 2
        for val = 0, num_values - 1 do
            current[var_id] = val
            recurse(index + 1, current)
        end
    end
    recurse(1, {})
    return combinations
end

local function assignment_to_key(assignment, var_ids)
    local key = {}
    for _, var_id in ipairs(var_ids) do
        table.insert(key, var_id)
        table.insert(key, assignment[var_id])
    end
    return table.concat(key, "_")
end

local function build_factor_from_cpt(model, var_id, pt, pt_to_dependents, var_num_values)
    local variables = {var_id}
    local dependents = pt_to_dependents[pt] or {}
    for _, dep_id in ipairs(dependents) do
        table.insert(variables, dep_id)
    end
    
    -- Create a new prob_table for this factor (copy of original)
    local dependents_vector = util.new_vector("int", true)
    for _, dep_id in ipairs(dependents) do
        dependents_vector:push_back(dep_id)
    end
    
    local num_values = model:prob_table_get_num_values(pt)
    local new_pt = model:prob_table_new(num_values, dependents_vector)
    
    -- Copy all entries from original prob_table
    local combos = generate_combinations(dependents, var_num_values)
    for _, combo in ipairs(combos) do
        local deps_values_table = {}
        for i, dep_id in ipairs(dependents) do
            deps_values_table[i - 1] = combo[dep_id]
        end
        
        for val = 0, num_values - 1 do
            local prob = model:prob_table_get_prob_entry(pt, val, deps_values_table)
            model:prob_table_set_prob_entry(new_pt, val, deps_values_table, prob)
        end
    end
    
    return {pt = new_pt, variables = variables}
end

local function multiply_factors(model, f1, f2, var_num_values)
    -- Handle Lua table factors (from empty variable cases)
    if #f1.variables == 0 and f1.table then
        if #f2.variables == 0 and f2.table then
            local result = {variables = {}, table = {}}
            for k1, v1 in pairs(f1.table) do
                for k2, v2 in pairs(f2.table) do
                    result.table[k1 .. k2] = v1 * v2
                end
            end
            return result
        else
            local result = {pt = f2.pt, variables = f2.variables}
            for val = 0, model:prob_table_get_num_values(f2.pt) - 1 do
                local deps_values = {}
                local prob = model:prob_table_get_prob_entry(f2.pt, val, deps_values) or 0
                for _, scalar in pairs(f1.table) do
                    model:prob_table_set_prob_entry(result.pt, val, deps_values, prob * scalar)
                    break
                end
            end
            return result
        end
    end
    
    if #f2.variables == 0 and f2.table then
        local result = {pt = f1.pt, variables = f1.variables}
        for val = 0, model:prob_table_get_num_values(f1.pt) - 1 do
            local deps_values = {}
            local prob = model:prob_table_get_prob_entry(f1.pt, val, deps_values) or 0
            for _, scalar in pairs(f2.table) do
                model:prob_table_set_prob_entry(result.pt, val, deps_values, prob * scalar)
                break
            end
        end
        return result
    end
    
    -- Merge variable lists
    local all_vars = {}
    local var_set = {}
    
    for _, v in ipairs(f1.variables) do
        if not var_set[v] then
            var_set[v] = true
            table.insert(all_vars, v)
        end
    end
    
    for _, v in ipairs(f2.variables) do
        if not var_set[v] then
            var_set[v] = true
            table.insert(all_vars, v)
        end
    end
    
    -- Determine dependents (all variables except the first)
    local dependents = {}
    for i = 2, #all_vars do
        table.insert(dependents, all_vars[i])
    end
    
    -- Create new prob_table for result
    local dependents_vector = util.new_vector("int", true)
    for _, dep_id in ipairs(dependents) do
        dependents_vector:push_back(dep_id)
    end
    
    local num_values = var_num_values[all_vars[1]] or 2
    local new_pt = model:prob_table_new(num_values, dependents_vector)
    
    -- Compute product for all combinations
    local combos = generate_combinations(all_vars, var_num_values)
    for _, combo in ipairs(combos) do
        -- Build deps_values for f1
        local deps_values1_table = {}
        for i = 2, #f1.variables do
            deps_values1_table[i - 2] = combo[f1.variables[i]]
        end
        local val1 = model:prob_table_get_prob_entry(f1.pt, combo[f1.variables[1]], deps_values1_table) or 0
        
        -- Build deps_values for f2
        local deps_values2_table = {}
        for i = 2, #f2.variables do
            deps_values2_table[i - 2] = combo[f2.variables[i]]
        end
        local val2 = model:prob_table_get_prob_entry(f2.pt, combo[f2.variables[1]], deps_values2_table) or 0
        
        -- Skip zero-probability entries
        if val1 ~= 0 and val2 ~= 0 then
            local deps_values_result_table = {}
            for i = 2, #all_vars do
                deps_values_result_table[i - 2] = combo[all_vars[i]]
            end
            model:prob_table_set_prob_entry(new_pt, combo[all_vars[1]], deps_values_result_table, val1 * val2)
        end
    end
    
    return {pt = new_pt, variables = all_vars}
end

local function max_marginalize(model, factor, var_id, var_num_values)
    local new_vars = {}
    for _, v in ipairs(factor.variables) do
        if v ~= var_id then
            table.insert(new_vars, v)
        end
    end
    
    if #new_vars == #factor.variables then
        return factor, {}
    end
    
    -- Handle empty new_vars case - use Lua table approach
    if #new_vars == 0 then
        local result = {
            variables = {},
            table = {}
        }
        local backpointers = {}
        local max_val = 0
        local best_val = 0
        local num_values_elim = var_num_values[var_id] or 2
        
        for val = 0, num_values_elim - 1 do
            local deps_values_table = {}
            local prob = model:prob_table_get_prob_entry(factor.pt, val, deps_values_table) or 0
            if prob > max_val then
                max_val = prob
                best_val = val
            end
        end
        
        result.table[""] = max_val
        backpointers[""] = best_val
        return result, backpointers
    end
    
    -- Determine dependents for new prob_table (all except first)
    local dependents = {}
    for i = 2, #new_vars do
        table.insert(dependents, new_vars[i])
    end
    
    -- Create new prob_table for result
    local dependents_vector = util.new_vector("int", true)
    for _, dep_id in ipairs(dependents) do
        dependents_vector:push_back(dep_id)
    end
    
    local num_values = var_num_values[new_vars[1]] or 2
    local new_pt = model:prob_table_new(num_values, dependents_vector)
    
    local backpointers = {}
    
    -- Max over eliminated variable
    local num_values_elim = var_num_values[var_id] or 2
    local combos = generate_combinations(new_vars, var_num_values)
    
    for ci, combo in ipairs(combos) do
        if ci % 65536 == 0 and util.lua_heap_over(LUA_HEAP_LIMIT_KB) then
            error({key="resource_limit", resource_limit=true}, 0)
        end
        local max_val = 0
        local best_val = 0
        
        for val = 0, num_values_elim - 1 do
            combo[var_id] = val
            
            -- Build deps_values for original factor
            local deps_values_table = {}
            for i = 2, #factor.variables do
                deps_values_table[i - 2] = combo[factor.variables[i]]
            end
            local prob = model:prob_table_get_prob_entry(factor.pt, combo[factor.variables[1]], deps_values_table) or 0
            
            if prob > max_val then
                max_val = prob
                best_val = val
            end
        end
        combo[var_id] = nil
        
        -- Set value in new prob_table
        local deps_values_result_table = {}
        for i = 2, #new_vars do
            deps_values_result_table[i - 2] = combo[new_vars[i]]
        end
        model:prob_table_set_prob_entry(new_pt, combo[new_vars[1]], deps_values_result_table, max_val)
        
        -- Store backpointer
        local key = assignment_to_key(combo, new_vars)
        backpointers[key] = best_val
    end
    
    return {pt = new_pt, variables = new_vars}, backpointers
end

local function sum_marginalize(model, factor, var_id, var_num_values)
    local new_vars = {}
    for _, v in ipairs(factor.variables) do
        if v ~= var_id then
            table.insert(new_vars, v)
        end
    end
    
    if #new_vars == #factor.variables then
        return factor
    end
    
    -- Handle empty new_vars case - use Lua table approach
    if #new_vars == 0 then
        local result = {
            variables = {},
            table = {}
        }
        local sum_val = 0
        local num_values_elim = var_num_values[var_id] or 2
        
        for val = 0, num_values_elim - 1 do
            local deps_values_table = {}
            local prob = model:prob_table_get_prob_entry(factor.pt, val, deps_values_table) or 0
            sum_val = sum_val + prob
        end
        
        result.table[""] = sum_val
        return result
    end
    
    -- Determine dependents for new prob_table (all except first)
    local dependents = {}
    for i = 2, #new_vars do
        table.insert(dependents, new_vars[i])
    end
    
    -- Create new prob_table for result
    local dependents_vector = util.new_vector("int", true)
    for _, dep_id in ipairs(dependents) do
        dependents_vector:push_back(dep_id)
    end
    
    local num_values = var_num_values[new_vars[1]] or 2
    local new_pt = model:prob_table_new(num_values, dependents_vector)
    
    -- Sum over eliminated variable
    local num_values_elim = var_num_values[var_id] or 2
    local combos = generate_combinations(new_vars, var_num_values)
    
    for _, combo in ipairs(combos) do
        local total = 0
        for val = 0, num_values_elim - 1 do
            combo[var_id] = val
            
            -- Build deps_values for original factor
            local deps_values_table = {}
            for i = 2, #factor.variables do
                deps_values_table[i - 2] = combo[factor.variables[i]]
            end
            local prob = model:prob_table_get_prob_entry(factor.pt, combo[factor.variables[1]], deps_values_table) or 0
            total = total + prob
        end
        combo[var_id] = nil
        
        -- Set value in new prob_table
        local deps_values_result_table = {}
        for i = 2, #new_vars do
            deps_values_result_table[i - 2] = combo[new_vars[i]]
        end
        model:prob_table_set_prob_entry(new_pt, combo[new_vars[1]], deps_values_result_table, total)
    end
    
    return {pt = new_pt, variables = new_vars}
end

local function restrict_factor(model, factor, var_id, value, var_num_values)
    local new_vars = {}
    for _, v in ipairs(factor.variables) do
        if v ~= var_id then
            table.insert(new_vars, v)
        end
    end
    
    -- Handle empty new_vars case - use Lua table approach
    if #new_vars == 0 then
        local result = {
            variables = {},
            table = {}
        }
        local deps_values_table = {}
        local prob = model:prob_table_get_prob_entry(factor.pt, value, deps_values_table) or 0
        result.table[""] = prob
        return result
    end
    
    -- Determine dependents for new prob_table (all except first)
    local dependents = {}
    for i = 2, #new_vars do
        table.insert(dependents, new_vars[i])
    end
    
    -- Create new prob_table for result
    local dependents_vector = util.new_vector("int", true)
    for _, dep_id in ipairs(dependents) do
        dependents_vector:push_back(dep_id)
    end
    
    local num_values = var_num_values[new_vars[1]] or 2
    local new_pt = model:prob_table_new(num_values, dependents_vector)
    
    -- Copy only entries where restricted variable has the specified value
    local combos = generate_combinations(new_vars, var_num_values)
    for _, combo in ipairs(combos) do
        combo[var_id] = value
        
        -- Build deps_values for original factor
        local deps_values_table = {}
        for i = 2, #factor.variables do
            deps_values_table[i - 2] = combo[factor.variables[i]]
        end
        local prob = model:prob_table_get_prob_entry(factor.pt, combo[factor.variables[1]], deps_values_table) or 0
        
        -- Set value in new prob_table
        local deps_values_result_table = {}
        for i = 2, #new_vars do
            deps_values_result_table[i - 2] = combo[new_vars[i]]
        end
        model:prob_table_set_prob_entry(new_pt, combo[new_vars[1]], deps_values_result_table, prob)
    end
    
    return {pt = new_pt, variables = new_vars}
end

local function compute_map(model, query_vars, cond, variable_name_to_id, pt_to_dependents, var_num_values, id_to_variable_name, var_value_names, evidence, atoms_list)
    -- Convert atoms_list to a set for quick lookup
    local atom_vars = {}
    if atoms_list then
        for _, var_name in ipairs(atoms_list) do
            atom_vars[var_name] = true
        end
    end
    
    local query_ids = {}
    for _, var_name in ipairs(query_vars) do
        table.insert(query_ids, variable_name_to_id[var_name])
    end
    
    local evidence_ids = {}
    for var_name, value_name in pairs(evidence) do
        local var_id = variable_name_to_id[var_name]
        if var_id then
            -- Convert value name to index
            local values = var_value_names[var_id]
            local value_index = 0
            for i, v in ipairs(values) do
                if v == value_name then
                    value_index = i - 1
                    break
                end
            end
            evidence_ids[var_id] = value_index
        end
    end
    
    local factors = {}
    local variable_ids = {}
    local parents_of = {}
    for i = 0, model.variables:size() - 1 do
        local var_id = model.variables[i]
        table.insert(variable_ids, var_id)
        local pt = model.variables_prob_tables[var_id]
        if pt then
            local factor = build_factor_from_cpt(model, var_id, pt, pt_to_dependents, var_num_values)
            -- the factor's child heads variables[] and its parents
            -- follow — record them before restriction rewrites the
            -- variable list (drives the ancestor-cone prune below)
            local pl = {}
            for pi = 2, #factor.variables do
                pl[#pl + 1] = factor.variables[pi]
            end
            parents_of[var_id] = pl

            -- Restrict factor by evidence immediately after building, like MPE solver
            for evidence_var_id, evidence_val in pairs(evidence_ids) do
                local contains = false
                for _, v in ipairs(factor.variables) do
                    if v == evidence_var_id then
                        contains = true
                        break
                    end
                end
                if contains then
                    factor = restrict_factor(model, factor, evidence_var_id, evidence_val, var_num_values)
                end
            end
            
            table.insert(factors, factor)
        end
    end
    
    -- Eliminate only the ancestor cone of query ∪ evidence.  A
    -- variable that is not ancestral to any query or evidence var is
    -- barren: its subtree's factor product marginalizes to 1 in the
    -- joint, so it can affect neither the joint over the query nor
    -- the argmax MAP reports (the answer is the assignment only).
    -- Dropping BOTH its factors and its elimination slot is therefore
    -- exact — this is the same cone solver_prob_var_elim restricts to,
    -- which is why P stays fast on nets where MAP blew up (the whole
    -- model elimination exhausted memory on munin).  Parents of a
    -- factor are the entries after the child in factor.variables; a
    -- barren child's restricted likelihood factors stay droppable too
    -- because its own ancestors of the evidence are kept via the e
    -- seed.  The earlier attempt pruned the elimination order only;
    -- leaving the factors in the product put irrelevant variables
    -- (e.g. atoms created by outer solvers such as value_compare)
    -- into the final factor.
    local relevant = {}
    local queue = {}
    local function seed(v)
        if v and not relevant[v] then
            relevant[v] = true
            queue[#queue + 1] = v
        end
    end
    for _, qid in ipairs(query_ids) do seed(qid) end
    for vid in pairs(evidence_ids) do seed(vid) end
    while #queue > 0 do
        local v = table.remove(queue)
        for _, p in ipairs(parents_of[v] or {}) do seed(p) end
    end
    local kept_factors = {}
    for _, factor in ipairs(factors) do
        local keep = true
        for _, v in ipairs(factor.variables) do
            if not relevant[v] then keep = false break end
        end
        if keep then
            kept_factors[#kept_factors + 1] = factor
        end
    end
    factors = kept_factors

    -- adjacency over the kept factors only — dropped factors would
    -- otherwise leave phantom edges that pollute the min-fill order
    local adjacency = {}
    for _, var_id in ipairs(variable_ids) do
        adjacency[var_id] = {}
    end
    for _, factor in ipairs(factors) do
        for i, v1 in ipairs(factor.variables) do
            for j, v2 in ipairs(factor.variables) do
                if i ~= j then
                    adjacency[v1][v2] = true
                    adjacency[v2][v1] = true
                end
            end
        end
    end

    local elimination_order = {}
    local remaining = {}
    local remaining_set = {}

    -- Build set of query variables
    local query_set = {}
    for _, qid in ipairs(query_ids) do
        query_set[qid] = true
    end

    for _, var_id in ipairs(variable_ids) do
        if relevant[var_id] and not query_set[var_id]
           and not evidence_ids[var_id] then
            table.insert(remaining, var_id)
            remaining_set[var_id] = true
        end
    end
    
    while #remaining > 0 do
        local min_fill = math.huge
        local min_var = remaining[1]
        
        for _, var_id in ipairs(remaining) do
            -- Count how many new edges would be added if we eliminate this variable
            local neighbors = {}
            for neighbor, _ in pairs(adjacency[var_id]) do
                if remaining_set[neighbor] then
                    table.insert(neighbors, neighbor)
                end
            end
            
            local new_edges = 0
            for i, n1 in ipairs(neighbors) do
                for j, n2 in ipairs(neighbors) do
                    if i < j and not adjacency[n1][n2] then
                        new_edges = new_edges + 1
                    end
                end
            end
            
            if new_edges < min_fill then
                min_fill = new_edges
                min_var = var_id
            end
        end
        
        -- Exact projection of the product factor's entry count
        -- ({min_var} ∪ remaining neighbours): any step whose factor
        -- would exceed the per-factor ceiling is known to hit the
        -- resource limit, so bail here instead of grinding toward it.
        local projected = var_num_values[min_var] or 2
        for neighbor in pairs(adjacency[min_var]) do
            if remaining_set[neighbor] then
                projected = projected * (var_num_values[neighbor] or 2)
                if projected > 2^22 then
                    error({key="resource_limit", resource_limit=true}, 0)
                end
            end
        end
        
        table.insert(elimination_order, min_var)
        remaining_set[min_var] = nil
        
        local new_remaining = {}
        for _, var_id in ipairs(remaining) do
            if var_id ~= min_var then
                table.insert(new_remaining, var_id)
            end
        end
        remaining = new_remaining
        
        local neighbors = {}
        for neighbor in pairs(adjacency[min_var]) do
            table.insert(neighbors, neighbor)
        end
        for i, n1 in ipairs(neighbors) do
            for j, n2 in ipairs(neighbors) do
                if i ~= j then
                    adjacency[n1][n2] = true
                    adjacency[n2][n1] = true
                end
            end
            adjacency[n1][min_var] = nil
            adjacency[min_var][n1] = nil
        end
    end
    
    local all_backpointers = {}
    
    for _, elim_var in ipairs(elimination_order) do
        if util.lua_heap_over(LUA_HEAP_LIMIT_KB) then
            error({key="resource_limit", resource_limit=true}, 0)
        end
        local new_factors = {}
        local to_multiply = {}
        
        for _, factor in ipairs(factors) do
            local contains = false
            for _, v in ipairs(factor.variables) do
                if v == elim_var then
                    contains = true
                    break
                end
            end
            if contains then
                table.insert(to_multiply, factor)
            else
                table.insert(new_factors, factor)
            end
        end
        
        if #to_multiply > 0 then
            local product = to_multiply[1]
            for i = 2, #to_multiply do
                product = multiply_factors(model, product, to_multiply[i], var_num_values)
            end
            local marginalized = sum_marginalize(model, product, elim_var, var_num_values)
            table.insert(new_factors, marginalized)
        end
        
        factors = new_factors
    end
    
    local final_factor = factors[1] or {pt = 0, variables = {}}
    for i = 2, #factors do
        final_factor = multiply_factors(model, final_factor, factors[i], var_num_values)
    end
    
    -- Directly find best assignment for query variables from final factor
    local max_prob = 0
    local best_assignment = {}
    
    if final_factor.table then
        -- Lua table factor (empty variables case)
        local query_combos = generate_combinations(query_ids, var_num_values)
        for _, combo in ipairs(query_combos) do
            local key = assignment_to_key(combo, query_ids)
            local prob = final_factor.table[key] or 0
            
            if prob > max_prob then
                max_prob = prob
                best_assignment = combo
            end
        end
    else
        -- Prob_table factor
        -- Find which variable in final_factor.variables is a query variable
        local query_var_in_factor = nil
        for _, var_id in ipairs(final_factor.variables) do
            for _, qid in ipairs(query_ids) do
                if var_id == qid then
                    query_var_in_factor = var_id
                    break
                end
            end
            if query_var_in_factor then break end
        end
        
        if query_var_in_factor then
            local query_combos = generate_combinations(query_ids, var_num_values)
            for _, combo in ipairs(query_combos) do
                local deps_values_table = {}
                local deps_index = 0
                
                -- Build deps_values_table for all variables in final_factor except the query variable
                for i, var_id in ipairs(final_factor.variables) do
                    if var_id ~= query_var_in_factor then
                        deps_values_table[deps_index] = combo[var_id]
                        deps_index = deps_index + 1
                    end
                end
                
                -- Get the value for the query variable
                local query_var_value = combo[query_var_in_factor]
                
                if query_var_value ~= nil then
                    local prob = model:prob_table_get_prob_entry(final_factor.pt, query_var_value, deps_values_table) or 0
                    
                    if prob > max_prob then
                        max_prob = prob
                        best_assignment = combo
                    end
                end
            end
        end
    end
    
    local result = {}
    local meta = {}
    function meta.__tostring(t)
        local order = {}
        for k,_ in pairs(t) do
            table.insert(order, k)
        end
        table.sort(order)
        local str = {}
        table.insert(str, "{")
        for _,k in ipairs(order) do
            table.insert(str, k)
            table.insert(str, "↦")
            table.insert(str, t[k])
            table.insert(str, ",")
        end
        if str[#str] == "," then
            str[#str] = nil
        end
        table.insert(str, "}")
        return table.concat(str)
    end
    
    -- Convert assignment to result with actual value names.  Every
    -- query variable is reported — the MAP semantics is the argmax over
    -- ALL of X; variables occurring in the condition still get assigned
    -- (unlike MPE, whose query set is defined as the non-evidence vars).
    -- Only solver-internal atom variables are filtered out.
    for i, var_id in ipairs(query_ids) do
        local var_name = id_to_variable_name[var_id]
        -- Exclude atom variables from result
        if not atom_vars[var_name] then
            local value_index = best_assignment[var_id]
            if value_index ~= nil then
                local values = var_value_names[var_id]
                result[var_name] = values[value_index + 1] or tostring(value_index)
            end
        end
    end
    
    setmetatable(result, meta)
    return result
end

local function map_solver(model, query_vars, cond, options, evidence, atoms_list)
    local mutable_model, variable_name_to_id, id_to_variable_name, pt_to_dependents, var_num_values, var_value_names = convert_to_mutable_bn(model)
    
    local result = compute_map(mutable_model, query_vars, cond, variable_name_to_id, pt_to_dependents, var_num_values, id_to_variable_name, var_value_names, evidence, atoms_list)
    return result
end

local solver = {}

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local parameters = self.parameters
    local property = parameters.property
    return property:get_type() == "operator" and property:get_operator_name() == "map"
end

function solver:get_priority()
    return 2
end

function solver:get_name()
    return "map_var_elim"
end

function solver:check()
    local parameters = self.parameters
    local model = parameters.model
    local property = parameters.property
    local operator = property:get_operator()
    local idlist = operator.identifier_list or {}
    local n = property:get_num_children()
    local cond = nil
    if operator.has_condition or n > #idlist then
        cond = property:get_child(n)
    end
    local resolved_idlist = {}
    for _,var in ipairs(idlist) do
        var = bindings.resolve(parameters, var)
        assert(model:is_variable(var),
                {key="map_var_not_variable",
                 parameters={variable=var},
                 positional=property:get_positional()})
        resolved_idlist[#resolved_idlist + 1] = var
    end
    
    local saved_atoms_list = parameters.atoms_list
    local atoms_list = {}
    parameters.atoms_list = atoms_list

    local evidence = {}

    local atom_cond
    if cond and not (logic.is_identifier(cond) and cond:get_identifier() == "true") then
        -- a bare Boolean-domain variable is the claim "X = <truthy>"
        local check = boolean_claim.as_claim(parameters, cond) or cond
        local original_property = parameters.property
        parameters.property = check
        atom_cond = parameters.model_check(parameters)
        parameters.property = property
        -- a non-Boolean bare variable evaluates to its marginal table,
        -- not a claim atom — that is no evidence
        if type(atom_cond) ~= "string" or not model:is_variable(atom_cond) then
            error({key="not_boolean",
                   positional=cond:get_positional()})
        end
        evidence[atom_cond] = "T"
    end

    local result = map_solver(model, resolved_idlist, cond, parameters.options, evidence, atoms_list)
    for _,variable in ipairs(atoms_list) do
        model:remove_variable(variable)
    end
    parameters.atoms_list = saved_atoms_list

    local map_property = make_map_property(result, property:get_positional())
    if not map_property then
        return result
    end

    local original_property = parameters.property
    parameters.property = map_property
    local atom_name = parameters.model_check(parameters)
    parameters.property = original_property
    if parameters.result_map then
        parameters.result_map[atom_name] = result
    end
    return atom_name
end

return solver
