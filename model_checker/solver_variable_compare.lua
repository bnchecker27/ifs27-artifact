---
---

local dependence = require "model_checker.dependence"
local util = require "lib.util"
local compare_semantics = require "model_checker.operators_compare_semantics"
local compute_shared_order = require "model_checker.compute_shared_order"
local result_display = require "model_checker.result_display"
local varterm = require "logic.varterm"
local bindings = require "model_checker.bindings"

local function bool_to_distribution(input)
    if input then
        return {T=1.0, F=0.0}
    else
        return {T=0.0, F=1.0}
    end
end

local solver = {}

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local parameters = self.parameters
    local property = parameters.property
    if property:get_type() ~= "operator" then
        return false
    end
    if not compare_semantics[property:get_operator_name()] then
        return false
    end
    -- operands: identifiers (variable or outcome literal) plus, for
    -- the varterm family, DIST/RENAME literals, numeric literals and
    -- conditioned variables — anything with an outcome domain compares
    -- by shared-outcome order.  At least one side must be a varterm or
    -- both must be plain identifiers (the classic case); identifier vs
    -- number stays with numeric_compare's incomparable report.
    local function operand_ok(child)
        if child:get_type() == "identifier" then return true end
        if varterm.is_varterm(child) then return true end
        -- a conditioned variable has an outcome domain too
        if child:get_type() == "operator"
           and child:get_operator_name() == "conditional" then
            return true
        end
        return false
    end
    local c1, c2 = property:get_child(1), property:get_child(2)
    if not operand_ok(c1) or not operand_ok(c2) then
        return false
    end
    local function is_cond(c)
        return c:get_type() == "operator"
           and c:get_operator_name() == "conditional"
    end
    if is_cond(c1) or is_cond(c2) then
        -- "(X|C) = DIST(...)": a conditioned variable against a
        -- literal belongs here only when a varterm is involved —
        -- "(X|C) = x" stays with solver_conditional_compare
        return varterm.is_varterm(c1) or varterm.is_varterm(c2)
    end
    if varterm.is_varterm(c1) or varterm.is_varterm(c2) then
        return true
    end
    return c1:get_type() == "identifier" and c2:get_type() == "identifier"
end

function solver:get_priority()
    return 3
end

function solver:get_name()
    return "variable_compare"
end

local function make_variable_name(property)
    local as_string = tostring(property)
    local result = {}
    for i=1,#as_string do
        local letter = as_string:byte(i)
        if string.byte("a") <= letter and letter <= string.byte("z")
                or string.byte("A") <= letter and letter <= string.byte("Z")
                or string.byte("0") <= letter and letter <= string.byte("9")
                or string.byte("_") == letter
        then
            table.insert(result, string.char(letter))
        else
            table.insert(result, string.format("x%Xx", letter))
        end
    end
    result = table.concat(result)
    return result
end

local function compute_shared_order_map(list_1, list_2)
    local shared_order_list = compute_shared_order(list_1, list_2)
    local shared_order_map = {}
    for number,value in ipairs(shared_order_list) do
        shared_order_map[value] = number
    end
    return shared_order_map
end

local function make_comparison_node(model, property, atoms_list, parameters)
    -- the name is position-independent so that a repeated identical
    -- claim stays the same atom ("X = a ∧ X = a" is idempotent); when
    -- the comparison embeds a fresh literal (DIST/PDIST/mixture-MUX)
    -- the position suffix keeps the two occurrences distinct, as the
    -- literals' independence demands
    local new_variable_name = make_variable_name(property)
                            .. varterm.fresh_suffix(property)
    model:set_values(new_variable_name, {"F", "T"})
    -- resolve an operand to the name it compares under: an identifier
    -- is a variable or an outcome literal (a LET-bound name resolves
    -- to the variable it denotes); a DIST/RENAME literal or a
    -- conditioned variable materialises into its aux variable first
    local function operand_name(child)
        if child:get_type() == "identifier" then
            return bindings.resolve(parameters, child:get_identifier())
        end
        parameters.property = child
        local name = parameters.model_check(parameters)
        parameters.property = property
        return name
    end
    local left_operand = operand_name(property:get_child(1))
    local right_operand = operand_name(property:get_child(2))
    -- the variable set is read after materialisation so aux operands
    -- (a DIST/RENAME literal, a conditional aux) get real CPT rows
    local variables = util.list_to_set(model:get_variables())
    local left_values = model:get_values_or_nil(left_operand)
    local right_values = model:get_values_or_nil(right_operand)

    assert(left_values or right_values,
            {key="atom_no_variable",
             parameters={left=left_operand, right=right_operand},
             positional=property:get_positional()})

    if not left_values then
        local found = false
        for _, value in ipairs(right_values) do
            if value == left_operand then
                found = true
                break
            end
        end
        assert(found,
                {key="atom_invalid_value",
                 parameters={value=left_operand, variable=right_operand},
                 positional=property:get_child(1):get_positional()})
        left_values = {left_operand}
    end

    if not right_values then
        local found = false
        for _, value in ipairs(left_values) do
            if value == right_operand then
                found = true
                break
            end
        end
        assert(found,
                {key="atom_invalid_value",
                 parameters={value=right_operand, variable=left_operand},
                 positional=property:get_child(2):get_positional()})
        right_values = {right_operand}
    end

    -- Both operands name the same variable: the truth value is the same
    -- for every possible value, so the comparison result is independent of
    -- the variable.  The previous loop could not represent a single
    -- variable having two different values in one row, and overwrote the
    -- CPT randomly.
    if left_operand == right_operand then
        local bool_value = compare_semantics[property:get_operator_name()](1, 1)
        model:set_probabilies(new_variable_name, {}, bool_to_distribution(bool_value))
        table.insert(atoms_list, new_variable_name)
        result_display.comparison(parameters, new_variable_name, property)
        return new_variable_name
    end

    local shared_order_map = compute_shared_order_map(left_values, right_values)
    for _, left_value in ipairs(left_values) do
        for _, right_value in ipairs(right_values) do
            local left_value_number = shared_order_map[left_value]
            local right_value_number = shared_order_map[right_value]
            local bool_value = compare_semantics[property:get_operator_name()](left_value_number, right_value_number)
            local row = {}
            row[left_operand] = util.ternary(variables[left_operand], left_value, nil)
            row[right_operand] = util.ternary(variables[right_operand], right_value, nil)
            model:set_probabilies(new_variable_name, row, bool_to_distribution(bool_value))
        end
    end
    table.insert(atoms_list, new_variable_name)
    result_display.comparison(parameters, new_variable_name, property)
    return new_variable_name
end

function solver:check()
    local parameters = self.parameters

    return make_comparison_node(parameters.model, parameters.property, parameters.atoms_list, parameters)
end

return solver
