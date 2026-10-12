---
---

local logic = require "logic.logic"
local operators = require "logic.operators"
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

local evidence_solver = require "model_checker.evidencer"
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
    return 1
end

function solver:get_name()
    return "map_sample"
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

    local atom_cond
    if cond and logic.is_identifier(cond) and cond:get_identifier() == "true" then
        -- backward compat: explicit "true" evidence
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
    local result = evidence_solver(model, atom_cond, resolved_idlist, parameters.options)
    for _,variable in ipairs(atoms_list) do
        model:remove_variable(variable)
    end

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
