---
--- Lexical binding environment for LET ... IN formulas (feature "let").
---
--- solver_let keeps a map on `parameters.bindings`: source-level name ->
--- model/auxiliary variable name the name denotes.  Bound names are
--- scoped to a single formula evaluation: solver_let installs a fresh
--- scope table (extending any enclosing let's scope so nested lets see
--- outer bindings) and restores the previous value after the body was
--- checked.
---
--- Every solver that resolves an identifier into a variable name must
--- pass it through bindings.resolve so bound names work uniformly in
--- bare-variable formulas, P(...) marginals, comparisons, conditionals,
--- numeric expressions, MUX/RENAME sources, moments and query variable
--- lists.
---

local bindings = {}

-- name -> the variable it denotes in the current scope (itself when
-- unbound).  `parameters` may be nil/absent for callers that only ever
-- see model variables.
function bindings.resolve(parameters, name)
    local env = parameters and parameters.bindings
    return (env and env[name]) or name
end

return bindings
