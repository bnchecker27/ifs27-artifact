---
---

local make_sampler = require "model_checker.sampler_auto"
local compute_graphs = require "model_checker.compute_graphs"
local find_reachable = require "model_checker.find_reachable"
local make_bn = require "bayesian_network.bayesian_network"
local features_lib = require "lib.features"
local varterm = require "logic.varterm"
local bindings = require "model_checker.bindings"
local boolean_claim = require "model_checker.boolean_claim"

local function find_relevant(model, node, cond)
    local _,graph = compute_graphs(model)
    local start = {}
    table.insert(start, node)
    if cond then
        table.insert(start, cond)
    end
    return find_reachable(graph, start)
end

local function restrict_to_node_list(original, reachable)
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

local function prob_solver(model, node, cond, options)
    local relevant = find_relevant(model, node, cond)
    model = restrict_to_node_list(model, relevant)
    local naive_solver = make_sampler(model, options)
    local node_number = naive_solver:get_variable_to_number(node)
    local cond_number = naive_solver:get_variable_to_number(cond)
    local total = 0
    local total_not = 0
    local function callback(assignment, weight)
        if not cond_number or assignment[cond_number] == 1 then
            if assignment[node_number] == 1 then
                total = weight + total
            else
                total_not = weight + total_not
            end
        end
    end
    naive_solver:set_callback(callback)
    naive_solver:run()
    assert(total + total_not > 0, {key="zero_probability_evidence"})
    return total / (total + total_not)
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
        if t == "identifier" then has_var = true return true end
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

-- sampled counterpart of prob_var_elim's marginal_distribution: count
-- each outcome of the query variable over the (evidence-consistent)
-- samples
local function marginal_solver(model, node, cond, options)
    local relevant = find_relevant(model, node, cond)
    model = restrict_to_node_list(model, relevant)
    local naive_solver = make_sampler(model, options)
    local node_number = naive_solver:get_variable_to_number(node)
    local cond_number = naive_solver:get_variable_to_number(cond)
    local declared = model:get_values(node)
    local order = sorted_order(declared)
    local counts = {}
    local total = 0
    local function callback(assignment, weight)
        if not cond_number or assignment[cond_number] == 1 then
            local value = assignment[node_number]
            counts[value] = (counts[value] or 0) + weight
            total = total + weight
        end
    end
    naive_solver:set_callback(callback)
    naive_solver:run()
    assert(total > 0, {key="zero_probability_evidence"})
    local dist = {}
    for i, value in ipairs(declared) do
        dist[value] = (counts[i - 1] or 0) / total
    end
    return setmetatable(dist, {__order = order})
end

local solver = {}

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local parameters = self.parameters
    local property = parameters.property
    return property:get_type() == "operator" and property:get_operator_name() == "prob"
end

function solver:get_priority()
    return 1
end

function solver:get_name()
    return "prob_sample"
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

    -- bare identifier asks for the variable's (conditional) marginal
    -- distribution — "marginal" feature: P(X), P(X | B).  Same routing
    -- as solver_prob_var_elim: a non-Boolean atom needs the conditional
    -- (cond-RV) or marginal reading, anything else is not_boolean
    local opts = parameters.options
    local feature_set = opts and (opts.get and opts:get("features")
                                  or opts.features)
    local atom_prob, marginal
    if prob:get_type() == "identifier" then
        -- a LET-bound name may denote a Boolean claim atom — P(B) is
        -- then the scalar probability like P(φ), no marginal query
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
            -- claim atom is not evidence
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
        -- unconditional marginal
        if atom_cond == atom_prob then
            atom_cond = nil
        end
        result = marginal_solver(model, atom_prob, atom_cond, parameters.options)
    elseif atom_cond == atom_prob then
        -- a claim conditioned on itself: P(φ | φ) = 1
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
