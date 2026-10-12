---
---

local compute_graphs = require "model_checker.compute_graphs"
local find_reachable = require "model_checker.find_reachable"
local mutable_bn = require "model_checker.mutable_bn"
local util = require "lib.util"
local features_lib = require "lib.features"
local varterm = require "logic.varterm"
local bindings = require "model_checker.bindings"
local boolean_claim = require "model_checker.boolean_claim"

-- Lua-heap ceiling: the ffi factor arena is metered inside mutable_bn, but
-- Lua-side structures can grow just as large; past this limit bail out with
-- a catchable resource_limit error so the dispatcher can fall back.
local LUA_HEAP_LIMIT_KB = 1536 * 1024

local function restrict_to_node_list(original, reachable)
    local make_bn = require "bayesian_network.bayesian_network"
    local result = make_bn()
    for _,node in ipairs(reachable) do
        local values = original:get_values(node)
        result:set_values(node, values)
    end
    for _,node in ipairs(reachable) do
        local probabilities = original:get_probabilities(node)
        result:set_probabilies(node, probabilities)
    end
    return result
end

local function find_relevant(model, node, cond)
    local _,graph = compute_graphs(model)
    local start = {}
    table.insert(start, node)
    if cond then
        table.insert(start, cond)
    end
    return find_reachable(graph, start)
end

local function convert_to_mutable_bn(original)
    local result = mutable_bn()
    local variable_name_to_id = {}
    local id_to_variable_name = {}
    local pt_to_dependents = {}  -- Store mapping from pt to dependent variable IDs
    local var_num_values = {}  -- Store number of values for each variable ID
    
    -- Add variables
    for _,node in ipairs(original:get_variables()) do
        local values = original:get_values(node)
        local num_values = #values
        local var_id = result:variable_add(num_values)
        variable_name_to_id[node] = var_id
        id_to_variable_name[var_id] = node
        var_num_values[var_id] = num_values
    end
    
    -- Add probability tables
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
        
        local num_values = #original:get_values(node)
        local pt = result:prob_table_new(num_values, dependents_vector)
        result:variable_set_prob_table(var_id, pt)
        
        -- Store dependent variable IDs for this prob table
        pt_to_dependents[pt] = dependents_ids
        
        -- Fill probability table
        local probabilities = original:get_probabilities(node)
        if next(probabilities) then
            for row, probs in pairs(probabilities) do
                local deps_values_table = {}
                for i,dep in ipairs(dependents) do
                    -- Convert string value to index
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
    
    return result, variable_name_to_id, id_to_variable_name, pt_to_dependents, var_num_values
end

-- Helper function to generate all combinations of variable values
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
        local num_values = var_num_values[var_id] or 2  -- Default to binary if not specified
        for val = 0, num_values - 1 do
            current[var_id] = val
            recurse(index + 1, current)
        end
    end
    recurse(1, {})
    return combinations
end

-- Build a factor from a CPT - returns prob_table with first variable as main
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

-- Multiply two factors using prob_tables (first variable is main)
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

-- Sum out a variable from a factor using prob_tables (first variable is main)
local function sum_out(model, factor, var_id, var_num_values)
    local new_vars = {}
    for _, v in ipairs(factor.variables) do
        if v ~= var_id then
            table.insert(new_vars, v)
        end
    end
    
    if #new_vars == #factor.variables then
        return factor  -- Variable not in factor
    end
    
    -- Handle empty new_vars case - use Lua table approach
    if #new_vars == 0 then
        local result = {
            variables = {},
            table = {}
        }
        local total = 0
        local num_values_elim = var_num_values[var_id] or 2
        
        for val = 0, num_values_elim - 1 do
            local deps_values_table = {}
            local prob = model:prob_table_get_prob_entry(factor.pt, val, deps_values_table) or 0
            total = total + prob
        end
        
        result.table[""] = total
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

-- Restrict factor to evidence using prob_tables (first variable is main)
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

-- eliminate every variable except `query_id` (evidence optionally
-- restricts its factors first) and return the remaining factor over the
-- query variable — callers read whichever value entries they need.
local function eliminate_to_factor(model, query_id, evidence_var, evidence_value, variable_name_to_id, pt_to_dependents, var_num_values)
    local evidence_id = evidence_var and variable_name_to_id[evidence_var]

    -- Build factors from CPTs (copy to new prob_tables for consistent indexing)
    local factors = {}
    local variable_ids = {}
    for i = 0, model.variables:size() - 1 do
        local var_id = model.variables[i]
        table.insert(variable_ids, var_id)
        local pt = model.variables_prob_tables[var_id]
        if pt then
            local factor = build_factor_from_cpt(model, var_id, pt, pt_to_dependents, var_num_values)
            table.insert(factors, factor)
        end
    end
    
    -- Apply evidence
    if evidence_id then
        local new_factors = {}
        for _, factor in ipairs(factors) do
            local contains = false
            for _, v in ipairs(factor.variables) do
                if v == evidence_id then
                    contains = true
                    break
                end
            end
            if contains then
                factor = restrict_factor(model, factor, evidence_id, evidence_value, var_num_values)
            end
            table.insert(new_factors, factor)
        end
        factors = new_factors
    end
    
    -- Build adjacency graph for elimination order heuristic
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
    
    -- Min-fill heuristic: eliminate variables that add fewest new edges
    -- Partial elimination: only eliminate variables that are d-separated from query
    local elimination_order = {}
    local remaining = {}
    local remaining_set = {}
    
    -- Eliminate all variables except the query.  The d-separation
    -- optimization that used to be here was too aggressive: it dropped
    -- variables that carry evidence, which made conditional queries on
    -- independent sub-networks appear to have zero probability.
    for _, var_id in ipairs(variable_ids) do
        if var_id ~= query_id then
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
        
        -- Update adjacency: connect neighbors of min_var
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
    
    -- Eliminate variables
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
            -- Multiply all factors containing elim_var
            local product = to_multiply[1]
            for i = 2, #to_multiply do
                product = multiply_factors(model, product, to_multiply[i], var_num_values)
            end
            
            -- Sum out elim_var
            product = sum_out(model, product, elim_var, var_num_values)
            table.insert(new_factors, product)
        end
        
        factors = new_factors
    end
    
    -- Multiply remaining factors
    local final_factor = factors[1] or {pt = 0, variables = {}}
    for i = 2, #factors do
        final_factor = multiply_factors(model, final_factor, factors[i], var_num_values)
    end
    return final_factor
end

local function variable_elimination(model, query_var, evidence_var, evidence_value, variable_name_to_id, pt_to_dependents, var_num_values)
    local query_id = variable_name_to_id[query_var]
    local final_factor = eliminate_to_factor(model, query_id, evidence_var, evidence_value, variable_name_to_id, pt_to_dependents, var_num_values)

    -- Get probability for query variable being true (value 1)
    local deps_values = {}
    local prob_true = model:prob_table_get_prob_entry(final_factor.pt, 1, deps_values) or 0

    local prob_false = model:prob_table_get_prob_entry(final_factor.pt, 0, deps_values) or 0

    local total = prob_true + prob_false
    if total > 0 then
        return prob_true / total
    end

    if evidence_var then
        error({key="zero_probability_evidence"})
    end

    return 0
end

local function prob_solver(model, node, cond, options)
    local relevant = find_relevant(model, node, cond)
    local restricted_model = restrict_to_node_list(model, relevant)
    local mutable_model, variable_name_to_id, id_to_variable_name, pt_to_dependents, var_num_values = convert_to_mutable_bn(restricted_model)
    
    local evidence_var = cond
    local evidence_value = 1  -- Assume condition is true
    
    local result = variable_elimination(mutable_model, node, evidence_var, evidence_value, variable_name_to_id, pt_to_dependents, var_num_values)
    
    return result
end

local function is_conditional(node)
    return node:get_type() == "operator"
        and node:get_operator_name() == "conditional"
end

-- a random-variable arithmetic term ("numvar" feature): an arithmetic
-- operator subtree with at least one identifier leaf — materialises
-- into a derived numeric variable
local ARITH_OPS = {plus = true, minus = true, times = true, divide = true}
local function is_numexpr(node)
    -- an arithmetic subtree whose leaves are only variable names and
    -- numeric constants, with at least one variable leaf — an
    -- identifier inside P(…) or a comparison belongs to that subformula
    if node:get_type() ~= "operator" then
        return false
    end
    if not ARITH_OPS[node:get_operator_name()] then
        return false
    end
    local has_var = false
    local function walk(nd)
        local t = nd:get_type()
        if t == "identifier" or varterm.is_varterm(nd) then
            has_var = true
            return true
        end
        if t == "value" then return true end
        if t ~= "operator" or not ARITH_OPS[nd:get_operator_name()] then
            return false
        end
        for i = 1, nd:get_num_children() do
            if not walk(nd:get_child(i)) then return false end
        end
        return true
    end
    return walk(node) and has_var
end

-- real-valued outcomes order numerically, not by declaration
local function sorted_order(values)
    local numeric = #values > 0
    for _, v in ipairs(values) do
        if type(v) ~= "number" then
            numeric = false
            break
        end
    end
    if not numeric then
        return values
    end
    local copy = {}
    for _, v in ipairs(values) do
        copy[#copy + 1] = v
    end
    table.sort(copy, function(a, b) return a < b end)
    return copy
end

-- Exact marginal distribution over a model variable: restrict to the
-- variable's ancestor cone, eliminate every other variable, and read
-- all of its values off the final factor (the prob query above reads
-- only the "true" entry).  An optional evidence atom ({F,T} variable)
-- turns it into the conditional marginal P(var | evidence).  Returns
-- {value_name = probability}.
local function marginal_distribution(model, var_name, evidence_var)
    local relevant = find_relevant(model, var_name, evidence_var)
    local restricted_model = restrict_to_node_list(model, relevant)
    local mutable_model, variable_name_to_id, _, pt_to_dependents, var_num_values = convert_to_mutable_bn(restricted_model)
    local final_factor = eliminate_to_factor(mutable_model, variable_name_to_id[var_name], evidence_var, 1, variable_name_to_id, pt_to_dependents, var_num_values)
    local dist, total = {}, 0
    local declared = restricted_model:get_values(var_name)
    for i, v in ipairs(declared) do
        local p = mutable_model:prob_table_get_prob_entry(final_factor.pt, i - 1, {}) or 0
        dist[v] = p
        total = total + p
    end
    -- __order lists outcomes in numeric order for real-valued
    -- variables, declaration order otherwise
    local order = sorted_order(declared)
    if total > 0 then
        for v, p in pairs(dist) do
            dist[v] = p / total
        end
    elseif evidence_var then
        error({key="zero_probability_evidence"})
    end
    -- __order keeps the node's declared outcome order for renderers
    -- (metatable, so plain pairs() consumers are unaffected)
    return setmetatable(dist, {__order = order})
end

local solver = {}

-- exposed for solver_variable (bare node name = marginal query)
solver.marginal_distribution = marginal_distribution

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local parameters = self.parameters
    local property = parameters.property
    return property:get_type() == "operator" and property:get_operator_name() == "prob"
end

function solver:get_priority()
    return 2  -- Higher priority than sampling
end

function solver:get_name()
    return "prob_var_elim"
end

function solver:check()
    local parameters = self.parameters
    local model = parameters.model
    local property = parameters.property
    local prob = property:get_child(1)
    local cond = property:get_child_or_nil(2)

    local saved_atoms_list = parameters.atoms_list
    local atoms_list = {}
    parameters.atoms_list = atoms_list

    local function get_atom(child)
        local original_property = parameters.property
        parameters.property = child
        local result = parameters.model_check(parameters)
        parameters.property = original_property
        return result
    end

    -- a bare identifier asks for the variable's (conditional) marginal
    -- distribution — "marginal" feature: P(X), P(X | B).  Claims and
    -- conditional terms materialise into atom variables first; a
    -- conditional aux over non-Boolean outcomes is a marginal query too
    local opts = parameters.options
    local feature_set = opts and (opts.get and opts:get("features")
                                  or opts.features)
    local atom_prob, marginal
    if prob:get_type() == "identifier" then
        -- model_check would resolve the identifier to its marginal
        -- table, leaving no atom for the factor machinery — require the
        -- feature flag up front instead of crashing downstream (the
        -- service validates this earlier; keep the direct path clean).
        -- A LET-bound name may denote a Boolean claim atom — P(B) is
        -- then the scalar probability like P(φ), no marginal query.
        atom_prob = bindings.resolve(parameters, prob:get_identifier())
        local values = model:get_values_or_nil(atom_prob)
        local bound_claim = parameters.bindings ~= nil
            and parameters.bindings[prob:get_identifier()] ~= nil
            and values ~= nil and #values == 2
            and values[1] == "F" and values[2] == "T"
        if bound_claim then
            marginal = false
        elseif features_lib.has(feature_set, "marginal") then
            marginal = values ~= nil
                and not (#values == 2 and values[1] == "F"
                         and values[2] == "T")
        else
            -- a bare Boolean-domain variable is the claim "X = <truthy
            -- outcome>": P(GOAL_2) means P(GOAL_2 = true)
            local claim = boolean_claim.as_claim(parameters, prob)
            if not claim then
                error({key="not_boolean",
                       positional=prob:get_positional()})
            end
            atom_prob = get_atom(claim)
            marginal = false
        end
    else
        atom_prob = get_atom(prob)
        local values = type(atom_prob) == "string"
                       and model:get_values_or_nil(atom_prob) or nil
        marginal = values ~= nil
            and not (#values == 2 and values[1] == "F" and values[2] == "T")
        if marginal and not is_conditional(prob)
            and not is_numexpr(prob)
            and not varterm.is_varterm(prob)
            and prob:get_operator_name() ~= "let" then
            -- a non-Boolean atom that is not a conditional term, a
            -- random-variable arithmetic term or a DIST/RENAME literal
            -- has no marginal reading
            error({key="not_boolean",
                   positional=prob:get_positional()})
        end
    end
    local atom_cond
    if cond and not (cond:get_type() == "identifier" and cond:get_identifier() == "true") then
        if cond:get_type() == "identifier" and parameters.bindings
           and parameters.bindings[cond:get_identifier()] then
            -- a LET-bound name in the evidence position denotes the
            -- bound claim's atom itself, not its marginal table
            atom_cond = parameters.bindings[cond:get_identifier()]
        else
            -- a bare Boolean-domain variable is the claim
            -- "X = <truthy outcome>"; anything not materialising into a
            -- claim atom (a non-Boolean variable's marginal table, a
            -- scalar) is not evidence
            atom_cond = get_atom(boolean_claim.as_claim(parameters, cond)
                                 or cond)
            if type(atom_cond) ~= "string"
               or not model:is_variable(atom_cond) then
                error({key="not_boolean",
                       positional=cond:get_positional()})
            end
        end
    end

    parameters.atoms_list = saved_atoms_list
    local result
    if marginal then
        -- P(X | X): a variable conditioned on itself reads as its
        -- unconditional marginal (the same result the unbound form
        -- gives, where the condition evaluates to a marginal table)
        if atom_cond == atom_prob then
            atom_cond = nil
        end
        result = marginal_distribution(model, atom_prob, atom_cond)
    elseif atom_cond == atom_prob then
        -- a claim conditioned on itself: P(φ | φ) = 1 — the factor
        -- machinery would restrict the query atom out of every factor
        result = 1
    else
        result = prob_solver(model, atom_prob, atom_cond, parameters.options)
    end
    for _,variable in ipairs(atoms_list) do
        model:remove_variable(variable)
    end
    return result
end

return solver
