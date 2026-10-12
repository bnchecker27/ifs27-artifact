---
--- logic/dist_family.lua — registry of the named finite-support
--- discrete distributions (feature "dists"), one entry per literal:
---
---   BERNOULLI(p)         {0,1}                 success probability p
---   RADEMACHER()         {-1,1}                uniform signs
---   BINOMIAL(n,p)        {0,..,n}              successes in n trials
---   BETABINOMIAL(n,a,b)  {0,..,n}              binomial with Beta(a,b)-mixed p
---   DEGENERATE(x)        {x}                   point mass (number or name)
---   DUNIF(a,b)           {a,..,b}              discrete uniform, a<=b integers
---   HYPERGEO(N,K,n)      draws without replacement: N items, K success
---                        states, n draws -> #successes drawn
---   NEGHYPGEO(N,K,r)     successes drawn before the r-th failure
---                        (Wikipedia parametrisation, support {0,..,K})
---   POIBIN(p1,..,pn)     {0,..,n}              successes of independent
---                        Bernoulli trials with individual probabilities
---   FHYPGEO(n1,n2,m,w)   Fisher's noncentral hypergeometric, odds w
---   WHYPGEO(n1,n2,m,w)   Wallenius' noncentral hypergeometric, odds w
---   BENFORD()            {1,..,9}              first-digit law
---   SOLITON(k)           {1,..,k}              ideal soliton
---   RSOLITON(k,c,d)      {1,..,k}              robust soliton
---   ZIPF(N,s)            {1,..,N}              power law
---   ZIPFM(N,q,s)         {1,..,N}              Zipf-Mandelbrot
---
--- All supports are numeric except DEGENERATE's name form.  Parameters
--- are positional literals (real numbers, or an identifier/name for
--- DEGENERATE).  Every spec:
---
---   kw        the uppercase literal keyword
---   params    ordered {name, kind} specs; kinds below
---   variadic  POIBIN: the single param kind applies to every argument
---   min/max   arity bounds (default: exactly #params)
---   defaults  argument text the formula-tree editor inserts on retype
---   check(a)  optional cross-parameter check -> nil or "pdist_param",params
---   pmf(a)    -> {values={..}, probs={..}} given valid args
---
--- LuaJIT / Lua 5.4 common subset.
---

local dist_family = {}

-- Lanczos approximation of ln(Gamma(z)), g=7, n=9 — enough for the
-- binomial-coefficient log-weights below (relative error ~1e-15)
local LANCZOS = {0.99999999999980993, 676.5203681218851,
                 -1259.1392167224028, 771.32342877765313,
                 -176.61502916214059, 12.507343278686905,
                 -0.13857109526572012, 9.9843695780195716e-6,
                 1.5056327351493116e-7}
local function lgamma(z)
    if z < 0.5 then
        return math.log(math.pi / math.sin(math.pi * z)) - lgamma(1 - z)
    end
    z = z - 1
    local x = LANCZOS[1]
    for i = 2, #LANCZOS do
        x = x + LANCZOS[i] / (z + i - 1)
    end
    local t = z + 7.5
    return 0.5 * math.log(2 * math.pi) + (z + 0.5) * math.log(t) - t
           + math.log(x)
end

local function logchoose(n, k)
    return lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)
end

-- k * ln(p) under pmf conventions: 0 * ln(p) = 0, k * ln(0) = -inf (k>0)
local function xlogy(k, p)
    if k == 0 then return 0 end
    if p <= 0 then return -math.huge end
    return k * math.log(p)
end

-- probabilities from unnormalised log-weights: exponentiate relative to
-- the maximum so extreme parameters cannot overflow, then normalise
local function normalize_logw(logw)
    local mx = -math.huge
    for _, w in ipairs(logw) do
        if w > mx then mx = w end
    end
    local probs, sum = {}, 0
    for i, w in ipairs(logw) do
        local p = math.exp(w - mx)
        probs[i] = p
        sum = sum + p
    end
    if not (sum > 0) or sum ~= sum then return nil end
    for i = 1, #probs do
        probs[i] = probs[i] / sum
    end
    return probs
end

local function irange(lo, hi)
    local out = {}
    for v = lo, hi do
        out[#out + 1] = v
    end
    return out
end

-- -- parameter kinds --------------------------------------------------
-- each: ok(value) and a `what` phrase for the pdist_param message
local function finite(v)
    return type(v) == "number" and v == v
           and v ~= math.huge and v ~= -math.huge
end
local KIND = {
    prob   = {what = "a probability in [0,1]",
              ok = function(v) return finite(v) and v >= 0 and v <= 1 end},
    unit01 = {what = "a number in (0,1]",
              ok = function(v) return finite(v) and v > 0 and v <= 1 end},
    nnint  = {what = "a non-negative integer",
              ok = function(v) return finite(v) and v >= 0
                                    and v == math.floor(v) end},
    posint = {what = "a positive integer",
              ok = function(v) return finite(v) and v >= 1
                                    and v == math.floor(v) end},
    int    = {what = "an integer",
              ok = function(v) return finite(v)
                                    and v == math.floor(v) end},
    pos    = {what = "a positive number",
              ok = function(v) return finite(v) and v > 0 end},
    nonneg = {what = "a non-negative number",
              ok = function(v) return finite(v) and v >= 0 end},
    lit    = {what = "a value (name or number)",
              ok = function(v) return type(v) == "number" or type(v) == "string" end},
}

local function spec(kw, params, pmf, extra)
    extra = extra or {}
    return {
        kw = kw,
        params = params,
        variadic = extra.variadic or false,
        min = extra.min or #params,
        max = extra.max or #params,
        defaults = extra.defaults,
        check = extra.check,
        pmf = pmf,
    }
end

-- hypergeometric support bounds: draws without replacement
local function hyper_support(N, K, n)
    return math.max(0, n + K - N), math.min(K, n)
end

local specs = {}

specs.bernoulli = spec("BERNOULLI",
    {{"p", "prob"}},
    function(a)
        return {values = {0, 1}, probs = {1 - a[1], a[1]}}
    end,
    {defaults = "0.5"})

specs.rademacher = spec("RADEMACHER", {},
    function()
        return {values = {-1, 1}, probs = {0.5, 0.5}}
    end,
    {defaults = ""})

specs.binomial = spec("BINOMIAL",
    {{"n", "nnint"}, {"p", "prob"}},
    function(a)
        local n, p = a[1], a[2]
        local vals, logw = {}, {}
        for k = 0, n do
            vals[#vals + 1] = k
            logw[#logw + 1] = logchoose(n, k) + xlogy(k, p)
                              + xlogy(n - k, 1 - p)
        end
        return {values = vals, probs = normalize_logw(logw)}
    end,
    {defaults = "10, 0.5"})

specs.betabinomial = spec("BETABINOMIAL",
    {{"n", "nnint"}, {"alpha", "pos"}, {"beta", "pos"}},
    function(a)
        local n, alpha, beta = a[1], a[2], a[3]
        local vals, logw = {}, {}
        local const = lgamma(alpha + beta) - lgamma(alpha) - lgamma(beta)
        for k = 0, n do
            vals[#vals + 1] = k
            logw[#logw + 1] = logchoose(n, k)
                              + lgamma(k + alpha) + lgamma(n - k + beta)
                              - lgamma(n + alpha + beta) + const
        end
        return {values = vals, probs = normalize_logw(logw)}
    end,
    {defaults = "10, 2, 5"})

specs.degenerate = spec("DEGENERATE",
    {{"x", "lit"}},
    function(a)
        return {values = {a[1]}, probs = {1}}
    end,
    {defaults = "x"})

specs.dunif = spec("DUNIF",
    {{"a", "int"}, {"b", "int"}},
    function(a)
        local lo, hi = a[1], a[2]
        local vals = irange(lo, hi)
        local p = 1 / #vals
        local probs = {}
        for i = 1, #vals do probs[i] = p end
        return {values = vals, probs = probs}
    end,
    {defaults = "1, 6",
     check = function(a)
         if a[2] < a[1] then
             return "pdist_param",
                    {family = "DUNIF", param = "b",
                     want = "an integer >= a", value = a[2], argi = 2}
         end
         return nil
     end})

specs.hypergeo = spec("HYPERGEO",
    {{"N", "nnint"}, {"K", "nnint"}, {"n", "nnint"}},
    function(a)
        local N, K, n = a[1], a[2], a[3]
        local lo, hi = hyper_support(N, K, n)
        local vals, logw = {}, {}
        for x = lo, hi do
            vals[#vals + 1] = x
            logw[#logw + 1] = logchoose(K, x) + logchoose(N - K, n - x)
        end
        return {values = vals, probs = normalize_logw(logw)}
    end,
    {defaults = "20, 8, 5",
     check = function(a)
         local N, K, n = a[1], a[2], a[3]
         if K > N then
             return "pdist_param",
                    {family = "HYPERGEO", param = "K",
                     want = "an integer <= N", value = K, argi = 2}
         end
         if n > N then
             return "pdist_param",
                    {family = "HYPERGEO", param = "n",
                     want = "an integer <= N", value = n, argi = 3}
         end
         return nil
     end})

-- successes drawn before the r-th failure (support {0,..,K});
-- P(X=k) = C(k+r-1,k) * C(N-k-r, K-k) / C(N,K)
specs.neghypgeo = spec("NEGHYPGEO",
    {{"N", "nnint"}, {"K", "nnint"}, {"r", "posint"}},
    function(a)
        local N, K, r = a[1], a[2], a[3]
        local vals, logw = {}, {}
        for k = 0, K do
            vals[#vals + 1] = k
            logw[#logw + 1] = logchoose(k + r - 1, k)
                              + logchoose(N - k - r, K - k)
        end
        return {values = vals, probs = normalize_logw(logw)}
    end,
    {defaults = "10, 4, 1",
     check = function(a)
         local N, K, r = a[1], a[2], a[3]
         if K > N then
             return "pdist_param",
                    {family = "NEGHYPGEO", param = "K",
                     want = "an integer <= N", value = K, argi = 2}
         end
         if r > N - K then
             return "pdist_param",
                    {family = "NEGHYPGEO", param = "r",
                     want = "an integer <= N - K", value = r, argi = 3}
         end
         return nil
     end})

-- Poisson binomial: convolution of the individual Bernoulli trials
specs.poibin = spec("POIBIN",
    {{"p", "prob"}},
    function(a)
        local probs = {1}
        for _, p in ipairs(a) do
            local nxt = {}
            for k = 1, #probs + 1 do
                nxt[k] = (probs[k] or 0) * (1 - p) + (probs[k - 1] or 0) * p
            end
            probs = nxt
        end
        return {values = irange(0, #a), probs = probs}
    end,
    {variadic = true, min = 0, max = math.huge, defaults = "0.5, 0.5"})

-- Fisher's noncentral hypergeometric: weights C(n1,x)*C(n2,m-x)*w^x
local function nchg_check(family)
    return function(a)
        local n1, n2, m = a[1], a[2], a[3]
        if m > n1 + n2 then
            return "pdist_param",
                   {family = family, param = "m",
                    want = "an integer <= n1 + n2", value = m, argi = 3}
        end
        return nil
    end
end

specs.fhypgeo = spec("FHYPGEO",
    {{"n1", "nnint"}, {"n2", "nnint"}, {"m", "nnint"}, {"omega", "pos"}},
    function(a)
        local n1, n2, m, w = a[1], a[2], a[3], a[4]
        local lo, hi = hyper_support(n1 + n2, n1, m)
        local vals, logw = {}, {}
        for x = lo, hi do
            vals[#vals + 1] = x
            logw[#logw + 1] = logchoose(n1, x) + logchoose(n2, m - x)
                              + xlogy(x, w)
        end
        return {values = vals, probs = normalize_logw(logw)}
    end,
    {defaults = "8, 12, 5, 2",
     check = nchg_check("FHYPGEO")})

-- Wallenius' noncentral hypergeometric: sequential draws where the next
-- type-1 item is taken with odds w*(n1-a) vs (n2-b) — a DP over the
-- draw lattice (a successes, b failures after a+b draws)
specs.whypgeo = spec("WHYPGEO",
    {{"n1", "nnint"}, {"n2", "nnint"}, {"m", "nnint"}, {"omega", "pos"}},
    function(a)
        local n1, n2, m, w = a[1], a[2], a[3], a[4]
        local function ptype1(aa, bb)
            local num = w * (n1 - aa)
            local den = num + (n2 - bb)
            if den <= 0 then return 0 end
            return num / den
        end
        local W = m + 1
        local P = {[1] = 1}   -- P(aa,bb) at index aa*W + bb + 1
        local function get(aa, bb) return P[aa * W + bb + 1] or 0 end
        local function set(aa, bb, v) P[aa * W + bb + 1] = v end
        for d = 1, m do
            for aa = math.min(d, n1), math.max(0, d - n2), -1 do
                local bb = d - aa
                local v = 0
                if aa > 0 then
                    v = v + get(aa - 1, bb) * ptype1(aa - 1, bb)
                end
                if bb > 0 then
                    v = v + get(aa, bb - 1) * (1 - ptype1(aa, bb - 1))
                end
                set(aa, bb, v)
            end
        end
        local lo, hi = hyper_support(n1 + n2, n1, m)
        local vals, probs = {}, {}
        for x = lo, hi do
            vals[#vals + 1] = x
            probs[#probs + 1] = get(x, m - x)
        end
        return {values = vals, probs = probs}
    end,
    {defaults = "8, 12, 5, 2",
     check = nchg_check("WHYPGEO")})

specs.benford = spec("BENFORD", {},
    function()
        local vals, probs = {}, {}
        local ln10 = math.log(10)
        for d = 1, 9 do
            vals[#vals + 1] = d
            probs[#probs + 1] = math.log(1 + 1 / d) / ln10
        end
        return {values = vals, probs = probs}
    end,
    {defaults = ""})

-- ideal soliton: rho(1) = 1/k, rho(d) = 1/(d*(d-1)) for d = 2..k
specs.soliton = spec("SOLITON",
    {{"k", "posint"}},
    function(a)
        local k = a[1]
        local vals, probs = {}, {}
        for d = 1, k do
            vals[#vals + 1] = d
            probs[#probs + 1] = d == 1 and 1 / k or 1 / (d * (d - 1))
        end
        return {values = vals, probs = probs}
    end,
    {defaults = "10"})

-- robust soliton: rho + tau over the normaliser beta, with
-- R = c*ln(k/delta)*sqrt(k) and the spike at floor(k/R)
specs.rsoliton = spec("RSOLITON",
    {{"k", "posint"}, {"c", "pos"}, {"delta", "unit01"}},
    function(a)
        local k, c, delta = a[1], a[2], a[3]
        local R = c * math.log(k / delta) * math.sqrt(k)
        local spike = math.max(1, math.floor(k / R))
        local vals, w = {}, {}
        for d = 1, k do
            local rho = d == 1 and 1 / k or 1 / (d * (d - 1))
            local tau = 0
            if d < spike then
                tau = R / (d * k)
            elseif d == spike then
                tau = R * math.log(R / delta) / k
            end
            vals[#vals + 1] = d
            w[#w + 1] = rho + tau
        end
        local sum = 0
        for _, v in ipairs(w) do sum = sum + v end
        for i = 1, #w do w[i] = w[i] / sum end
        return {values = vals, probs = w}
    end,
    {defaults = "10, 0.1, 0.5"})

specs.zipf = spec("ZIPF",
    {{"N", "posint"}, {"s", "nonneg"}},
    function(a)
        local N, s = a[1], a[2]
        local vals, logw = {}, {}
        for kk = 1, N do
            vals[#vals + 1] = kk
            logw[#logw + 1] = -s * math.log(kk)
        end
        return {values = vals, probs = normalize_logw(logw)}
    end,
    {defaults = "10, 1"})

specs.zipfm = spec("ZIPFM",
    {{"N", "posint"}, {"q", "nonneg"}, {"s", "nonneg"}},
    function(a)
        local N, q, s = a[1], a[2], a[3]
        local vals, logw = {}, {}
        for kk = 1, N do
            vals[#vals + 1] = kk
            logw[#logw + 1] = -s * math.log(kk + q)
        end
        return {values = vals, probs = normalize_logw(logw)}
    end,
    {defaults = "10, 2, 1"})

dist_family.specs = specs

-- ordered list of keywords (the Wikipedia section's order) and a
-- keyword -> spec map for the suggestion/parens machinery
dist_family.order = {
    "BERNOULLI", "RADEMACHER", "BINOMIAL", "BETABINOMIAL", "DEGENERATE",
    "DUNIF", "HYPERGEO", "NEGHYPGEO", "POIBIN", "FHYPGEO", "WHYPGEO",
    "BENFORD", "SOLITON", "RSOLITON", "ZIPF", "ZIPFM",
}
dist_family.keywords = {}
for name, spec in pairs(specs) do
    spec.name = name
    dist_family.keywords[spec.kw] = spec
end

-- validate the extracted argument literals of a pdist node:
-- arity, per-parameter kind, and the family's cross-parameter check.
-- Returns nil when valid, else an error key plus its parameters.
-- `masked[i]` marks an argument whose value is only decided at
-- evaluation (a LET-bound scalar): its kind check is skipped here —
-- the solver re-runs check_args on the resolved literals — and the
-- cross-parameter check is skipped entirely since it needs every
-- value.
function dist_family.check_args(spec, args, masked)
    if spec.variadic then
        if #args < spec.min then
            return "pdist_args",
                   {family = spec.kw, expected = ">= " .. spec.min,
                    got = #args}
        end
    elseif #args ~= #spec.params then
        return "pdist_args",
               {family = spec.kw, expected = #spec.params, got = #args}
    end
    for i, a in ipairs(args) do
        if not (masked and masked[i]) then
            local ps = spec.variadic and spec.params[1] or spec.params[i]
            local kind = KIND[ps[2]]
            if not kind.ok(a) then
                return "pdist_param",
                       {family = spec.kw, param = ps[1], want = kind.what,
                        value = tostring(a), argi = i}
            end
        end
    end
    if spec.check and not (masked and next(masked)) then
        return spec.check(args)
    end
    return nil
end

return dist_family
