---
--- Shared predicates for variable-valued terms (the "varterm" family):
--- terms that evaluate to a random variable rather than a Boolean
--- claim or a scalar number.
---
---   identifier          a model variable
---   DIST(o↦p,…)         distribution literal — fresh independent var
---   RENAME(term,o↦o',…) outcome renaming — dependent variable g(X)
---   MUX(S,o↦X,…)        multiplexer / MUX(X↦p,…) mixture ("mux")
---   FAMILY(arg,…)       named distribution literal — fresh independent
---                       variable (the "dists" feature; the operator
---                       name is the lowercase family name, e.g.
---                       "binomial", registered in logic/dist_family.lua)
---   numexpr             X + Y (the "numvar" feature)
---   term | claim        conditional random variable ("cond")
---
--- The model checker, the service validator and the suggestion layer
--- all need the same classification, so it lives here instead of being
--- re-derived per file.
---

local varterm = {}

local compute_shared_order = require "model_checker.compute_shared_order"
local dist_family = require "logic.dist_family"

local ARITH = {plus = true, minus = true, times = true, divide = true}

-- a DIST(...)/RENAME(...)/MUX(...)/FAMILY(...) literal node
function varterm.is_varterm(node)
    return node and node:get_type() == "operator"
        and (node:get_operator_name() == "dist"
             or node:get_operator_name() == "rename"
             or node:get_operator_name() == "mux"
             or dist_family.specs[node:get_operator_name()] ~= nil)
end

-- an arithmetic subtree over variable-valued leaves (identifiers,
--- numbers, DIST/RENAME literals) with at least one variable leaf —
--- the shape solver_numeric_expression materialises.  An identifier
--- inside P(…) or a comparison belongs to that subformula, not to the
--- expression's leaves.
function varterm.is_numexpr(node)
    if not node or node:get_type() ~= "operator" then
        return false
    end
    if not ARITH[node:get_operator_name()] then
        return false
    end
    local has_var = false
    local function walk(nd)
        local t = nd:get_type()
        if t == "identifier" or varterm.is_varterm(nd) then
            has_var = true
            return true
        end
        if t == "value" then
            return true
        end
        if t ~= "operator" or not ARITH[nd:get_operator_name()] then
            return false
        end
        for i = 1, nd:get_num_children() do
            if not walk(nd:get_child(i)) then
                return false
            end
        end
        return true
    end
    return walk(node) and has_var
end

-- a term that evaluates to a random variable: an identifier naming
--- one, a DIST/RENAME literal, a numexpr, a conditional whose own
--- left term is variable-valued, or a LET whose body is (the body
--- decides what the let denotes; syntactic only — a bound-name leaf
--- counts as a variable like any identifier)
function varterm.is_variable_term(node)
    if not node or type(node) ~= "table" or not node.get_type then
        return false
    end
    local t = node:get_type()
    if t == "identifier" then
        return true
    end
    if varterm.is_varterm(node) or varterm.is_numexpr(node) then
        return true
    end
    if t == "operator" then
        local op = node:get_operator_name()
        if op == "conditional" then
            return varterm.is_variable_term(node:get_child(1))
        end
        if op == "let" then
            return varterm.is_variable_term(
                node:get_child(node:get_num_children()))
        end
    end
    return false
end

-- the literal carried by a map-entry leaf: identifier → its name
--- (string), value → its number
function varterm.leaf_literal(node)
    local t = node:get_type()
    if t == "identifier" then
        return node:get_identifier()
    end
    if t == "value" then
        return node:get_value()
    end
    return nil
end

-- the two MUX forms share the same child list but read it
--- differently: "MUX(term ↦ real, …)" mixture children are all
--- branch↦weight entries, while "MUX(S, o ↦ X, …)" selector form
--- starts with the selector term followed by outcome↦branch entries.
--- The parser guarantees a mixture's first child is an "equal" node
--- whose right side is a real — that is exactly what distinguishes
--- the forms (a selector source is never such a node).
function varterm.mux_is_mixture(node)
    if not node or node:get_type() ~= "operator"
       or node:get_operator_name() ~= "mux" then
        return false
    end
    local c1 = node:get_child(1)
    return c1 ~= nil and c1:get_type() == "operator"
        and c1:get_operator_name() == "equal"
        and c1:get_child(2) ~= nil
        and c1:get_child(2):get_type() == "value"
end

-- the selector term of a selector-form MUX (nil for mixtures)
function varterm.mux_selector(node)
    if varterm.mux_is_mixture(node) then
        return nil
    end
    return node:get_child(1)
end

-- the map-entry children (selector form: children 2..n; mixture: all)
function varterm.mux_entries(node)
    local entries = {}
    local from = varterm.mux_is_mixture(node) and 1 or 2
    for i = from, node:get_num_children() do
        entries[#entries + 1] = node:get_child(i)
    end
    return entries
end

-- the branch terms of a MUX: selector form takes each entry's value
--- child ("o ↦ branch"), the mixture each entry's key ("branch ↦ p").
--- Non-entry children are skipped — validation reports them.
function varterm.mux_branches(node)
    local branches = {}
    local mixture = varterm.mux_is_mixture(node)
    for _, entry in ipairs(varterm.mux_entries(node)) do
        if entry:get_type() == "operator"
           and entry:get_operator_name() == "equal" then
            branches[#branches + 1] =
                entry:get_child(mixture and 1 or 2)
        end
    end
    return branches
end

-- merge two outcome lists under the MUX domain rule: identical or
--- unambiguously ordered — numbers sort numerically, strings merge
--- via compute_shared_order.  Returns nil for mixed kinds or when
--- the string merge is ambiguous/conflicting.
local function merge_domains(list_a, list_b)
    local kind = nil
    for _, list in ipairs({list_a, list_b}) do
        for _, v in ipairs(list) do
            local k = type(v) == "number" and "numeric" or "string"
            if kind and kind ~= k then
                return nil
            end
            kind = k
        end
    end
    if kind == "numeric" then
        local seen, out = {}, {}
        for _, list in ipairs({list_a, list_b}) do
            for _, v in ipairs(list) do
                if not seen[v] then
                    seen[v] = true
                    out[#out + 1] = v
                end
            end
        end
        table.sort(out)
        return out
    end
    local ok, merged = pcall(compute_shared_order, list_a, list_b)
    return ok and merged or nil
end

-- the declared output domain of a DIST/RENAME literal in order, known
--- statically: DIST's keys, or RENAME's new names (each in order of
--- first appearance — a merged name occurs once).  For MUX the
--- branch domains merge when all of them are statically known —
--- identifier or numexpr branches make it return nil (the domain is
--- resolved against the model instead).  Returns nil for
--- non-varterm nodes.
function varterm.domain(node)
    if not varterm.is_varterm(node) then
        return nil
    end
    local out, seen = {}, {}
    local opname = node:get_operator_name()
    local pdist = dist_family.specs[opname]
    if pdist then
        -- the support is a pure function of the literal arguments —
        -- an unfillable/invalid argument leaves the domain unresolved
        local args = {}
        for i = 1, node:get_num_children() do
            local v = varterm.leaf_literal(node:get_child(i))
            if v == nil then return nil end
            args[i] = v
        end
        if dist_family.check_args(pdist, args) then
            return nil
        end
        local d = pdist.pmf(args)
        return d and d.values or nil
    elseif opname == "dist" then
        for i = 1, node:get_num_children() do
            local v = varterm.leaf_literal(node:get_child(i):get_child(1))
            out[#out + 1] = v
        end
    elseif opname == "mux" then
        local merged = nil
        for _, branch in ipairs(varterm.mux_branches(node)) do
            -- a bare-number branch is a point mass on that numeric
            -- outcome; an identifier may be a named constant, which
            -- the static path cannot tell apart from a variable — it
            -- leaves the domain unresolved instead
            local bd = branch:get_type() == "value"
                       and {branch:get_value()}
                       or varterm.domain(branch)
            if not bd then
                return nil
            end
            merged = merged and merge_domains(merged, bd) or bd
            if not merged then
                return nil
            end
        end
        return merged
    else
        for i = 2, node:get_num_children() do
            local v = varterm.leaf_literal(node:get_child(i):get_child(2))
            if not seen[v] then
                seen[v] = true
                out[#out + 1] = v
            end
        end
    end
    return out
end

-- does the subtree contain a per-occurrence-fresh random variable?
-- A DIST or named-distribution literal is fresh at every textual
-- position, and so is a mixture-form MUX (its implicit selector is a
-- fresh independent draw).  Aux variables materialised from such a
-- subtree need a position-unique name — two textually identical
-- subformulas are then distinct variables, as the literals demand —
-- while a literal-free subtree keeps its position-independent name so
-- that e.g. "X = a ∧ X = a" stays idempotent.
function varterm.has_fresh_literal(node)
    if not node or node:get_type() ~= "operator" then
        return false
    end
    local opname = node:get_operator_name()
    if opname == "dist" or dist_family.specs[opname] ~= nil then
        return true
    end
    if opname == "mux" and varterm.mux_is_mixture(node) then
        return true
    end
    for i = 1, node:get_num_children() do
        if varterm.has_fresh_literal(node:get_child(i)) then
            return true
        end
    end
    return false
end

-- the aux-name suffix a subtree needs: the occurrence's byte offset
-- when it contains a fresh literal, "" otherwise — appended to the
-- formula-text-derived name by every materialising solver
function varterm.fresh_suffix(node)
    if not varterm.has_fresh_literal(node) then return "" end
    local pos = node:get_positional()
    return "x_" .. (pos and pos.from or 0)
end

-- "numeric" when every declared outcome is a number, "string" when
--- they are all names, nil for mixed domains or non-varterm nodes
function varterm.domain_kind(node)
    local domain = varterm.domain(node)
    if not domain or #domain == 0 then
        return nil
    end
    local kind = nil
    for _, v in ipairs(domain) do
        local k = type(v) == "number" and "numeric" or "string"
        if kind and kind ~= k then
            return nil
        end
        kind = k
    end
    return kind
end

return varterm
