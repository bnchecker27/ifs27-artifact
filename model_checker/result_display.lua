---
--- Human-readable displays for solver-internal result atoms.
---
--- Solvers that evaluate a (sub-)formula into an auxiliary Boolean model
--- variable ("atom") return that variable's name.  Query solvers (MAP,
--- MPE) additionally register their actual answer table in
--- `parameters.result_map`.  Composite solvers register a readable
--- rendering of their atom in `parameters.display_map`: the conjunction
--- over two MAP atoms then displays as
--- "(Grade = Low, SAT = Low) ∧ (Letter = Weak)" instead of leaking the
--- mangled internal variable name.
---
--- model_checker.model_checker resolves the top-level result through
--- result_map first (query answers), then the deterministic check
--- (true/false for decided formulas), then display_map (readable claims
--- for stochastic compounds), and only then leaves the raw value.

local result_display = {}

-- "A = a, B = b" — the assignment rendering shared with the service and
-- command line result formatting.  A table carrying a declared outcome
-- order (marginal_distribution's __order metatable) renders in that
-- order — lowest outcome first, as the BN node specifies it.
function result_display.assignment(result_table)
    local mt = getmetatable(result_table)
    local order = mt and mt.__order
    if order then
        local parts = {}
        for _, k in ipairs(order) do
            parts[#parts + 1] = tostring(k) .. " = " .. tostring(result_table[k])
        end
        return table.concat(parts, ", ")
    end
    local parts = {}
    for k, v in pairs(result_table) do
        table.insert(parts, tostring(k) .. " = " .. tostring(v))
    end
    table.sort(parts)
    return table.concat(parts, ", ")
end

-- Display for a sub-result: the registered query answer (MAP/MPE
-- assignment), a previously composed display, or the subformula text.
local function sub_display(parameters, child_property, child_result)
    local result_map = parameters.result_map
    if result_map then
        local registered = result_map[child_result]
        if type(registered) == "table" then
            return result_display.assignment(registered)
        elseif registered ~= nil then
            return tostring(registered)
        end
    end
    local display_map = parameters.display_map
    if display_map and display_map[child_result] then
        return display_map[child_result]
    end
    return tostring(child_property)
end

-- Does `s` already read as a single self-delimiting term — call-style
-- text like "IDP(Sprinkler,WetGrass)", a fully parenthesised group, or
-- a bare atom?  Then it needs no parens as a composed operand.
local function self_delimiting(s)
    if s:match("^[%w_%.]+$") then
        return true
    end
    if s:sub(-1) ~= ")" then
        return false
    end
    local open = s:find("(", 1, true)
    if not open or s:sub(1, open - 1):find("[%s%(%)]") then
        return false
    end
    return s:match("%b()", open) == s:sub(open)
end

-- Operand display inside a composed formula: the sub-result wrapped in
-- parens unless it is already self-delimiting.
local function operand_display(parameters, child_property, child_result)
    local s = sub_display(parameters, child_property, child_result)
    if self_delimiting(s) then
        return s
    end
    return "(" .. s .. ")"
end

-- Register a composed display for a Boolean operator atom: each operand
-- shows its query result when it produced one, else the subformula
-- text, and is parenthesised unless already self-delimiting —
-- "(d1) ∧ (d2)", "¬(d1)", "(d1) ⊕ IDP(A,B)".
function result_display.compose(parameters, atom_name, property, child_results)
    local display_map = parameters.display_map
    if not display_map then
        return
    end
    local operator = property:get_operator()
    local symbol = operator.default_symbol or property:get_operator_name()
    if operator.arity == 1 then
        display_map[atom_name] = symbol
                .. operand_display(parameters, property:get_child(1), child_results[1])
        return
    end
    local parts = {}
    for i = 1, operator.arity do
        parts[i] = operand_display(parameters, property:get_child(i), child_results[i])
    end
    display_map[atom_name] = table.concat(parts, " " .. symbol .. " ")
end

-- Register "left symbol right" for a comparison atom whose operands are
-- formula leaves — "Grade = High", "ℙ(Grade=High) > 0.5".
function result_display.comparison(parameters, atom_name, property)
    local display_map = parameters.display_map
    if not display_map then
        return
    end
    local operator = property:get_operator()
    local symbol = operator.default_symbol or property:get_operator_name()
    display_map[atom_name] = tostring(property:get_child(1))
            .. " " .. symbol .. " " .. tostring(property:get_child(2))
end

return result_display
