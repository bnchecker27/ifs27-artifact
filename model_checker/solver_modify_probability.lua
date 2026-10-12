---
---

local util = require "lib.util"
local bindings = require "model_checker.bindings"
local boolean_claim = require "model_checker.boolean_claim"

local function rows_equal(row1, row2)
    for k, v in pairs(row1) do
        if row2[k] ~= v then
            return false
        end
    end
    for k, v in pairs(row2) do
        if row1[k] ~= v then
            return false
        end
    end
    return true
end

local function find_matching_row(variable_probabilities, condition)
    for row, probs in pairs(variable_probabilities) do
        if rows_equal(row, condition) then
            return row, probs
        end
    end
    return nil, nil
end

local solver = {}

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local parameters = self.parameters
    local property = parameters.property
    return property:get_type() == "operator" and property:get_operator_name() == "modify_probability"
end

function solver:get_priority()
    return 1
end

function solver:get_name()
    return "modify_probability"
end

function solver:check()
    local parameters = self.parameters
    local model = parameters.model
    local property = parameters.property
    local model_check = parameters.model_check
    local operator = property:get_operator()
    -- LET-bound names resolve to the variable they denote, for the
    -- intervention target and the condition variables alike
    local identifier = bindings.resolve(parameters, operator.identifier)
    local condition = {}
    for cond_var, cond_val in pairs(operator.condition) do
        condition[bindings.resolve(parameters, cond_var)] = cond_val
    end
    assert(model:is_variable(identifier),
            {key="modify_prob_var_not_variable",
             parameters={variable=identifier},
             positional=property:get_positional()})
    local valid_values = model:get_values(identifier)
    local value_set = util.list_to_set(valid_values)
    local prob_map = operator.prob_map
    for value, _ in pairs(prob_map) do
        assert(value_set[value],
                {key="modify_prob_invalid_value",
                 parameters={variable=identifier, value=value},
                 positional=property:get_positional()})
    end
    for cond_var, cond_val in pairs(condition) do
        assert(model:is_variable(cond_var),
                {key="modify_prob_cond_var_not_variable",
                 parameters={variable=cond_var},
                 positional=property:get_positional()})
        local c_values = util.list_to_set(model:get_values(cond_var))
        assert(c_values[cond_val],
                {key="modify_prob_cond_invalid_value",
                 parameters={variable=cond_var, value=cond_val},
                 positional=property:get_positional()})
    end

    local all_probabilities = model:get_probabilities(identifier)

    local function modify_row(row, old_probabilities)
        local new_sum_mapped = 0
        local old_sum_mapped = 0
        for k,_ in pairs(prob_map) do
            new_sum_mapped = new_sum_mapped + prob_map[k]
            old_sum_mapped = old_sum_mapped + old_probabilities[k]
        end
        assert(not (old_sum_mapped == 1 and new_sum_mapped < 1),
                {key="undefined_cpt_update",
                 parameters={variable=identifier},
                 positional=property:get_positional()})
        local new_probabilities = {}
        for k,_ in pairs(old_probabilities) do
            if prob_map[k] then
                new_probabilities[k] = prob_map[k]
            else
                new_probabilities[k] = old_probabilities[k] * (1 - new_sum_mapped) / (1 - old_sum_mapped)
            end
        end
        return new_probabilities
    end

    local saved_rows = {}
    local modified_rows = {}

    if next(condition) == nil then
        -- Unconditional modification: update every CPT row.
        assert(next(all_probabilities),
                {key="modify_prob_row_not_found",
                 parameters={variable=identifier, condition="{}"},
                 positional=property:get_positional()})
        for row, old_probabilities in pairs(all_probabilities) do
            table.insert(saved_rows, {row = row, old_probabilities = old_probabilities})
            table.insert(modified_rows, {row = row, new_probabilities = modify_row(row, old_probabilities)})
        end
    else
        -- Conditional modification: update the matching CPT row.
        local row, old_probabilities = find_matching_row(all_probabilities, condition)
        assert(old_probabilities,
                {key="modify_prob_row_not_found",
                 parameters={variable=identifier, condition=tostring(condition)},
                 positional=property:get_positional()})
        table.insert(saved_rows, {row = row, old_probabilities = old_probabilities})
        table.insert(modified_rows, {row = row, new_probabilities = modify_row(row, old_probabilities)})
    end

    for _,entry in ipairs(modified_rows) do
        model:set_probabilies(identifier, entry.row, entry.new_probabilities)
    end

    local inner = property:get_child(1)
    -- a bare Boolean-domain variable is the claim "X = <truthy
    -- outcome>": P(GOAL_2[u]) is P(GOAL_2 = true [u]), not a marginal
    parameters.property = boolean_claim.as_claim(parameters, inner)
                          or inner
    local result = model_check(parameters)
    parameters.property = property

    for _,entry in ipairs(saved_rows) do
        model:set_probabilies(identifier, entry.row, entry.old_probabilities)
    end

    return result
end

return solver
