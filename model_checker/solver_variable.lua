---
--- Solver for a bare variable name: "Grade" is a complete formula asking
--- for the variable's marginal distribution.  The exact answer comes
--- from variable elimination (solver_prob_var_elim's factor machinery),
--- not a sampling estimate.  A LET-bound name resolves through
--- parameters.bindings to the variable it denotes.
---

local prob_var_elim = require "model_checker.solver_prob_var_elim"
local bindings = require "model_checker.bindings"

local solver = {}

function solver:set_parameters(parameters)
    self.parameters = parameters
end

function solver:can_handle()
    local property = self.parameters.property
    return property:get_type() == "identifier"
        and self.parameters.model:is_variable(
            bindings.resolve(self.parameters, property:get_identifier()))
end

function solver:get_priority()
    return 1
end

function solver:get_name()
    return "variable"
end

function solver:check()
    local parameters = self.parameters
    local name = bindings.resolve(parameters,
        parameters.property:get_identifier())
    -- a LET-bound name may denote an auxiliary atom (a claim's {F,T}
    -- variable, a literal's variable): Boolean operators and the
    -- evidence machinery need the atom itself, and the top-level
    -- resolution turns it into its display or marginal — a real model
    -- variable (or bound alias) asks for its marginal directly
    if parameters.display_map and parameters.display_map[name] then
        return name
    end
    return prob_var_elim.marginal_distribution(parameters.model, name)
end

return solver
