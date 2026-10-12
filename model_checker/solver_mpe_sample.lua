---
---

local util = require "lib.util"
local logic = require "logic.logic"
local operators = require "logic.operators"
local evidence_solver = require "model_checker.evidencer"
local bindings = require "model_checker.bindings"
local boolean_claim = require "model_checker.boolean_claim"

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

local function make_mpe_property(result, positional)
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
local solver = {}

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local parameters = self.parameters
    local property = parameters.property
    return property:get_type() == "operator" and property:get_operator_name() == "mpe"
end

function solver:get_priority()
    return 1
end

function solver:get_name()
    return "mpe_sample"
end

local function extract_evidence_vars(formula, result)
    if logic.is_identifier(formula) then
        local identifier = formula:get_identifier()
        if identifier then
            local var_name, value_name = identifier:match("([^=]+)=([^=]+)")
            if var_name and value_name then
                result[var_name] = true
            else
                -- a bare Boolean-domain variable is evidence, too
                result[identifier] = true
            end
        end
        return
    elseif logic.is_operator(formula) then
        local op_name = formula:get_operator_name()
        local children = formula:get_children()

        if (op_name == "=" or op_name == "equal") and #children == 2 then
            local var_name = children[1]:get_identifier()
            if var_name then
                result[var_name] = true
            end
        else
            for _, child in ipairs(children) do
                extract_evidence_vars(child, result)
            end
        end
    end
end

function solver:check()
    local parameters = self.parameters
    local model = parameters.model
    local property = parameters.property
    local cond = property:get_child_or_nil(1)

    local saved_atoms_list = parameters.atoms_list
    local atoms_list = {}
    parameters.atoms_list = atoms_list

    local cond_vars_to_exclude = {}
    if cond then
        extract_evidence_vars(cond, cond_vars_to_exclude)
    end
    local variables = util.list_to_set(model:get_variables())
    for var_name, _ in pairs(cond_vars_to_exclude) do
        variables[bindings.resolve(parameters, var_name)] = nil
    end
    -- aux atoms created by earlier operands of the enclosing formula
    -- (a sibling's MAP/P atom) are internal variables, never listed
    for _, variable in ipairs(saved_atoms_list) do
        variables[variable] = nil
    end
    variables = util.set_to_list(variables)

    local atom_cond
    if cond and logic.is_identifier(cond) and cond:get_identifier() == "true" then
        atom_cond = "true"
        model:set_values(atom_cond, {"F", "T"})
        model:set_probabilies(atom_cond, {}, {T=1.0, F=0.0})
        table.insert(atoms_list, atom_cond)
    elseif cond then
        -- a bare Boolean-domain variable is the claim "X = <truthy>";
        -- anything not materialising into a claim atom is not evidence
        local check = boolean_claim.as_claim(parameters, cond) or cond
        local original_property = parameters.property
        parameters.property = check
        atom_cond = parameters.model_check(parameters)
        parameters.property = property
        if type(atom_cond) ~= "string" or not model:is_variable(atom_cond) then
            error({key="not_boolean",
                   positional=cond:get_positional()})
        end
    end

    parameters.atoms_list = saved_atoms_list
    local result = evidence_solver(model, atom_cond, variables, parameters.options)
    for _,variable in ipairs(atoms_list) do
        model:remove_variable(variable)
    end

    local mpe_property = make_mpe_property(result, property:get_positional())
    if not mpe_property then
        return result
    end

    local original_property = parameters.property
    parameters.property = mpe_property
    local atom_name = parameters.model_check(parameters)
    parameters.property = original_property
    if parameters.result_map then
        parameters.result_map[atom_name] = result
    end
    return atom_name
end

return solver
