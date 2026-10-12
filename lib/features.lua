---
--- Optional feature flags shared by the parser, the service and the
--- solvers.  Features are off by default and enabled per request / per
--- command line via a comma separated list ("cond,marginal") or the
--- "all" keyword which enables every known feature.
---

local features = {}

-- every optional feature known to the system; "all" expands to this set
local KNOWN = {
    marginal = true,  -- P(A) / P(A|B) with a random variable A -> its
                      -- (conditional) marginal distribution (used by the
                      -- GUI demonstrator's node inspection)
    chart = true,     -- Result-row distribution chart (GUI only)
    numval = true,    -- real-valued outcomes + numeric comparisons
                      -- (benchmark models spell numeric domains as
                      -- numbers, e.g. pigs/link outcomes "0","1","2")
    arith = true,     -- accepted no-op: "+"/"÷" are built-in scalar
                      -- operators next to "−"/"×"
}

local IMPLIES = {}

-- parse("cond,marginal") -> {cond=true, marginal=true}; accepts a string
-- or an already-parsed set.  Unknown names are ignored so that a client
-- asking for a newer feature still works with an older server.
function features.parse(value)
    if type(value) == "table" then
        return value
    end
    local result = {}
    if type(value) ~= "string" then
        return result
    end
    for name in value:gmatch("[^,%s]+") do
        if name == "all" then
            for known in pairs(KNOWN) do
                result[known] = true
            end
        elseif KNOWN[name] then
            result[name] = true
        end
    end
    for name in pairs(result) do
        for implied in pairs(IMPLIES[name] or {}) do
            result[implied] = true
        end
    end
    return result
end

-- features.has(set_or_string, "cond") -> boolean
function features.has(value, name)
    return features.parse(value)[name] == true
end

return features
