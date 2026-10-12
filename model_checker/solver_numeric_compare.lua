---
--- Solver for comparisons with a numeric side (features "numval" /
--- "numvar"): a real literal or a random-variable arithmetic term
--- against a variable, or two real-valued variables against each
--- other.
---
---   X = 0.5        — equality against a numeric outcome
---   X < 0.5        — order against a real threshold
---   X < Y          — two real-valued variables compare numerically
---                    (declared outcome sets need not interleave)
---   X − Y > 0.5    — a materialised derived variable compares by value
---   (X|C) = 0.5    — a conditioned real variable against a number
---
--- Non-identifier operands are materialised first (numexpr → aux
--- variable, conditional → its aux), so the atom's parents are exactly
--- the variables carrying each side's value.  Pure identifier-vs-
--- outcome comparisons stay with solver_variable_compare.
---

local compare_semantics = require "model_checker.operators_compare_semantics"
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

local arithmetic_names = {plus=true, minus=true, times=true, divide=true}

local function is_conditional(child)
    return child:get_type() == "operator"
        and child:get_operator_name() == "conditional"
end

-- a numeric expression materialises through solver_numeric_expression:
-- an arithmetic subtree whose leaves are only variable names and
-- numeric constants, with at least one variable leaf.  An identifier
-- nested inside P(…) or a comparison belongs to that subformula.
local function is_numexpr(child)
    if child:get_type() ~= "operator" then
        return false
    end
    if not arithmetic_names[child:get_operator_name()] then
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
        if t ~= "operator"
           or not arithmetic_names[nd:get_operator_name()] then
            return false
        end
        for i = 1, nd:get_num_children() do
            if not walk(nd:get_child(i)) then return false end
        end
        return true
    end
    return walk(child) and has_var
end

local function is_numeric_values(values)
    if not values then return false end
    for _, v in ipairs(values) do
        if type(v) ~= "number" then
            return false
        end
    end
    return true
end

-- child kinds: "ident" names a variable or outcome, "num" is a real
-- literal, "numexpr"/"cond"/"varterm" materialise into aux variables
local function child_kind(child)
    if child:get_type() == "identifier" then return "ident" end
    if child:get_type() == "value" then return "num" end
    if is_numexpr(child) then return "numexpr" end
    if is_conditional(child) then return "cond" end
    if varterm.is_varterm(child) then return "varterm" end
    return "other"
end

-- does a varterm child declare a numeric domain?  DIST keys / RENAME
-- new names are known statically, so comparability can be decided
-- before anything is materialised
local function varterm_numeric(child)
    return varterm.domain_kind(child) == "numeric"
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
    local kl = child_kind(property:get_child(1))
    local kr = child_kind(property:get_child(2))
    if kl == "other" or kr == "other" then
        return false
    end
    if kl == "ident" and kr == "ident" then
        -- identifier-identifier is solver_variable_compare's domain —
        -- claim it only when both sides are variables and at least one
        -- is real-valued
        local model = parameters.model
        local lv = model:get_values_or_nil(bindings.resolve(parameters,
            property:get_child(1):get_identifier()))
        local rv = model:get_values_or_nil(bindings.resolve(parameters,
            property:get_child(2):get_identifier()))
        return lv ~= nil and rv ~= nil
           and (is_numeric_values(lv) or is_numeric_values(rv))
    end
    -- a conditional compared with an identifier keeps its dedicated
    -- solver ("(X|C) = x"); against a number/numexpr it is numeric
    if (kl == "cond" and kr == "ident") or (kl == "ident" and kr == "cond") then
        return false
    end
    -- a DIST/RENAME literal as operand: claim the comparison when a
    -- numeric reading is possible — the literal's own domain is known
    -- statically, the other side's may need materialisation.  A
    -- string-domain literal facing another string-domain term belongs
    -- to solver_variable_compare's shared-outcome semantics instead.
    if kl == "varterm" or kr == "varterm" then
        local vk = kl == "varterm" and property:get_child(1)
                                 or property:get_child(2)
        local ok = kl == "varterm" and kr or kl
        local other = kl == "varterm" and property:get_child(2)
                                    or property:get_child(1)
        if varterm_numeric(vk) then
            -- numeric literal: the other side must not be an outcome
            -- literal — a bare identifier only fits when it names a
            -- variable, a string-domain varterm leaves to variable_compare
            if ok == "ident" then
                return parameters.model:get_values_or_nil(
                           bindings.resolve(parameters,
                           other:get_identifier())) ~= nil
            end
            if ok == "varterm" then
                return varterm_numeric(other)
            end
            return true
        end
        -- string-domain literal: only a definitely-numeric other side
        -- is claimed (it reports the incomparable pair); identifier
        -- and string-domain operands stay with variable_compare
        if ok == "num" or ok == "numexpr" then
            return true
        end
        if ok == "ident" then
            local v = parameters.model:get_values_or_nil(
                          bindings.resolve(parameters,
                          other:get_identifier()))
            return v ~= nil and is_numeric_values(v)
        end
        if ok == "varterm" then
            return varterm_numeric(other)
        end
        return false
    end
    return true
end

function solver:get_priority()
    return 5  -- above variable_compare/value_compare/conditional_compare
end

function solver:get_name()
    return "numeric_compare"
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

function solver:check()
    local parameters = self.parameters
    local property = parameters.property
    local model = parameters.model
    local new_variable_name = make_variable_name(property)
                            .. varterm.fresh_suffix(property)

    -- resolve a side to {var=name, values={..}} or {const=c}; variables
    -- materialise through model_check (numexpr aux, conditional aux)
    local function resolve(child)
        local kind = child_kind(child)
        if kind == "num" then
            return {const = child:get_value()}
        end
        if kind == "ident" then
            local name = bindings.resolve(parameters, child:get_identifier())
            local values = model:get_values_or_nil(name)
            return {var = name, values = values, node = child}
        end
        parameters.property = child
        local name = parameters.model_check(parameters)
        parameters.property = property
        return {var = name, values = model:get_values_or_nil(name), node = child}
    end

    local left = resolve(property:get_child(1))
    local right = resolve(property:get_child(2))

    -- a bare identifier side must name a variable
    for _, side in ipairs({left, right}) do
        if side.var and not side.values then
            error({key="atom_no_variable",
                   parameters={left=side.var, right=side.var},
                   positional=side.node:get_positional()})
        end
    end

    -- numeric compatibility: a variable side must be real-valued
    for _, side in ipairs({left, right}) do
        if side.values and not is_numeric_values(side.values) then
            error({key="comparison_incomparable",
                   parameters={left=tostring(property:get_child(1)),
                               right=tostring(property:get_child(2))},
                   positional=property:get_positional()})
        end
    end

    -- "X = 0.5" requires the literal to be an outcome of X
    if property:get_operator_name() == "equal" then
        local function check_member(side, other)
            if side.const ~= nil and other.values then
                local found = false
                for _, v in ipairs(other.values) do
                    if v == side.const then
                        found = true
                        break
                    end
                end
                assert(found,
                       {key="atom_invalid_value",
                        parameters={value=tostring(side.const),
                                    variable=other.var},
                        positional=property:get_positional()})
            end
        end
        check_member(left, right)
        check_member(right, left)
    end

    model:set_values(new_variable_name, {"F", "T"})

    -- collect the parent variables (deduplicated: "X < X" has one)
    local parents = {}
    local parent_set = {}
    for _, side in ipairs({left, right}) do
        if side.var and not parent_set[side.var] then
            parent_set[side.var] = true
            table.insert(parents, side.var)
        end
    end
    local parent_values = {}
    local total = 1
    for _, name in ipairs(parents) do
        local values = (left.var == name and left.values)
                    or (right.var == name and right.values)
        parent_values[#parent_values + 1] = values
        total = total * #values
    end

    local function side_value(side, row)
        if side.const ~= nil then
            return side.const
        end
        return row[side.var]
    end

    if total == 0 then total = 1 end
    for i = 0, total - 1 do
        local rest = i
        local row = {}
        for j, name in ipairs(parents) do
            local values = parent_values[j]
            local idx = math.floor(rest % #values) + 1
            rest = math.floor(rest / #values)
            row[name] = values[idx]
        end
        local bool_value = compare_semantics[property:get_operator_name()](
            side_value(left, row), side_value(right, row))
        model:set_probabilies(new_variable_name, row,
                              bool_to_distribution(bool_value))
    end
    table.insert(parameters.atoms_list, new_variable_name)
    result_display.comparison(parameters, new_variable_name, property)
    return new_variable_name
end

return solver
