---
---

local util = require "lib.util"
local prob_var_elim = require "model_checker.solver_prob_var_elim"

local model_check_rec

function model_check_rec(parameters)
    local property = parameters.property
    assert(property)
    local limit_error
    for _,solver in ipairs(parameters.solvers) do
        solver:set_parameters(parameters)
        if solver:can_handle() then
            local ok, result = pcall(solver.check, solver)
            if ok then
                return result
            end
            if type(result) ~= "table" or not result.resource_limit then
                error(result, 0)
            end
            -- The solver exceeded a resource ceiling rather than failing
            -- semantically: a lower-priority (approximate) solver that also
            -- accepts this property may still produce an answer.
            io.stderr:write(("solver %s hit the memory limit; trying a cheaper solver\n"):format(
                tostring(solver:get_name())))
            limit_error = result
        end
    end
    if limit_error then
        error(limit_error, 0)
    end
    error({key="cannot_handle_property",
           parameters={property=tostring(property)},
           positional=property:get_positional()})
end

local function compare_solver_priority(solver_1, solver_2)
    return solver_1:get_priority() > solver_2:get_priority()
end


local function validate_solver_name(solver_name)
    local valid_solvers = {
        "arithmetic_operator", "boolean_operator", "idp", "infl", "modify_probability", "numeric_compare", "prob_sample", "prob_var_elim", "value", "value_compare", "variable", "variable_compare", "map_sample", "map_var_elim", "mpe_sample", "mpe_var_elim"
    }
    local valid_solver_set = util.list_to_set(valid_solvers)
    if not valid_solver_set[solver_name] then
        error({key="invalid_solver_name", parameters={solver=solver_name}})
    end
end

local function collect_solvers(options)
    local solvers = { "arithmetic_operator", "boolean_operator", "idp", "infl", "modify_probability", "numeric_compare", "prob_var_elim", "value", "value_compare", "variable", "variable_compare", "map_var_elim", "mpe_var_elim"}
    if options:get("solvers") then
        solvers = util.split(options:get("solvers"), ",")
        for _,solver in ipairs(solvers) do
            validate_solver_name(solver)
        end
    end
    solvers = util.list_to_set(solvers)
    if options:get("disable_solvers") then
        local disable = util.split(options:get("disable_solvers"), ",")
        for _,d in ipairs(disable) do
            validate_solver_name(d)
            solvers[d] = nil
        end
    end
    if options:get("enable_solvers") then
        local enable = util.split(options:get("enable_solvers"), ",")
        for _,d in ipairs(enable) do
            validate_solver_name(d)
            solvers[d] = true
        end
    end
    solvers = util.set_to_list(solvers)
    local solver_instances = {}
    for _,solver_name in ipairs(solvers) do
        local solver = require("model_checker.solver_" .. solver_name)
        assert(solver, solver_name)
        table.insert(solver_instances, solver)
    end
    table.sort(solver_instances, compare_solver_priority)
    return solver_instances
end

local function is_bool_variable(model, variable)
    local values = model:get_values_or_nil(variable)
    return values and #values == 2 and values[1] == "F" and values[2] == "T"
end

local function compute_marginal(model, variable, memo)
    if memo[variable] then
        return memo[variable]
    end
    local dist = {}
    local all_probs = model:get_probabilities(variable)
    for row, probs in pairs(all_probs) do
        local row_prob = 1
        for parent, value in pairs(row) do
            local parent_dist = compute_marginal(model, parent, memo)
            row_prob = row_prob * (parent_dist[value] or 0)
        end
        if row_prob > 0 then
            for value, p_cond in pairs(probs) do
                dist[value] = (dist[value] or 0) + p_cond * row_prob
            end
        end
    end
    memo[variable] = dist
    return dist
end

local function coerce_to_boolean(model, result)
    if not is_bool_variable(model, result) then
        return result
    end
    local memo = {}
    local dist = compute_marginal(model, result, memo)
    if math.abs((dist.T or 0) - 1) < 1E-9 then
        return true
    elseif math.abs((dist.F or 0) - 1) < 1E-9 then
        return false
    end
    return result
end

local function model_check(model, property, options)
    assert(model)
    assert(property)
    local parameters = {}
    parameters.model = model
    parameters.property = property
    parameters.options = options
    parameters.solvers = collect_solvers(options)
    parameters.atoms_list = {}
    parameters.bindings = nil   -- solver_let installs the name->variable scope
    parameters.result_map = {}
    parameters.display_map = {}
    parameters.model_check = model_check_rec
    local result = model_check_rec(parameters)
    if type(result) == "string" and parameters.result_map[result] then
        -- Registered query answer (MAP/MPE assignment).
        result = parameters.result_map[result]
    elseif type(result) == "string" and model:is_variable(result) then
        -- Decided formulas report their truth value; stochastic
        -- compounds fall back to their readable display (registered by
        -- the solver that built the atom) so the internal variable name
        -- never leaks to the user.
        result = coerce_to_boolean(model, result)
        if type(result) == "string" and not is_bool_variable(model, result) then
            -- a non-Boolean atom — a conditional random variable's aux:
            -- the result is its (conditional) marginal distribution
            result = prob_var_elim.marginal_distribution(model, result)
        elseif type(result) == "string" and parameters.display_map[result] then
            result = parameters.display_map[result]
        end
    end
    for _,variable in ipairs(parameters.atoms_list) do
        model:remove_variable(variable)
    end
    return result
end

-- The module stays callable (model_check) so existing callers keep
-- working; the solver plumbing is also exposed via collect_solvers.
return setmetatable({
    check = model_check,
    collect_solvers = collect_solvers,
}, {
    __call = function(_, model, property, options)
        return model_check(model, property, options)
    end,
})
