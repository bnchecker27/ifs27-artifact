---
---

local lpeg = require "lpeg"
local logic = require "logic.logic"
local lpeg_util = require "lib.lpeg_util"
local parsing_context = require "lib.parsing_context"
local make_positional = require "lib.positional"

local Space = lpeg_util.Space
local Open = lpeg_util.Open
local Close = lpeg_util.Close
local Bar = lpeg_util.Bar

local function make_parser(aps, context, feature_set, phi_sub_holder)
    local function make_prob(pos_from, left, right, pos_to)
        pos_to = pos_to - 1
        local prob_op = {
            is_operator=true,
            name="prob",
            arity=1,
            precedence=8,
            notation="postfix",
            associativity="none",
            associative=false,
        }
        if right then
            prob_op.arity = 2
        end

        function prob_op.tostring(what)
            local result = {}
            table.insert(result, "ℙ")
            table.insert(result, "(")
            table.insert(result, tostring(what.children[1]))
            if what.children[2] then
                table.insert(result, "|")
                table.insert(result, tostring(what.children[2]))
            end
            table.insert(result, ")")
            result = table.concat(result)
            return result
        end
        local positional = make_positional(context.input, pos_from, pos_to)
        if right then
            return logic.make_binary_operator(left, right, prob_op, positional)
        else
            return logic.make_unary_operator(left, prob_op, positional)
        end
    end
    local function make_prob_cond(pos_from, left, right, pos_to)
        return make_prob(pos_from, left, right, pos_to)
    end
    local function make_prob_no_cond(pos_from, left, pos_to)
        return make_prob(pos_from, left, nil, pos_to)
    end

    -- Canonical spelling is the double-struck ℙ (like 𝔼/𝕍); 𝒫 (mathcal
    -- style) remains a parseable alias so older formulas still work.
    local P = lpeg_util.string_array_S({"P", "ℙ", "𝒫"}) * Space
    local OpenOrError = lpeg_util.labeled(Open, "expected_lparen", {kw="("})
    -- ")" / "|" inside P(..) are only offerable when the argument can
    -- still become a probability query: a claim always does, a bare
    -- variable term only under "marginal".  The operand that just
    -- completed rides in the payload as `after` (see lpeg_util.track).
    local function close_gate(after)
        return {kw = ")", gate = "probarg", after = after}
    end
    local function bar_gate(after)
        return {kw = "|", gate = "probarg", after = after}
    end
    local function claim_close_gate(after)
        return {kw = ")", gate = "claimarg", after = after}
    end
    local CloseOrError = lpeg_util.suggestable_after(Close, close_gate)
                       + context:Label("expected_rparen")
    -- the evidence bar is a separator note so the operand-chain walk
    -- recognises "query | evidence" (its owner stamp is "P")
    local BarNote = lpeg_util.sep_note(lpeg.P"|", "pbar") * Space
    local BarOrError = lpeg_util.suggestable_after(BarNote, bar_gate)
                     + context:Label("expected_bar")
    local ClaimCloseOrError = lpeg_util.suggestable_after(Close, claim_close_gate)
                            + context:Label("expected_rparen")

    -- the argument is a Boolean-claim slot inside P's parens: payloads
    -- and operand ends in the interior carry the stamp so the resolver
    -- knows e.g. "P(x | …" is evidence position
    local function scoped(inner)
        return lpeg_util.sug_scope(inner,
            {slot = "bool", owner = "P", in_p = true})
    end

    -- Without the "cond" feature there is no infix "|" operator, so the
    -- classic two-alternative grammar "P(phi | phi) | P(phi)" is exact.
    if not (feature_set and feature_set.cond) then
        return context:Cp() * P * OpenOrError * scoped(aps * BarOrError * aps * ClaimCloseOrError) * context:Cp() / make_prob_cond
             + context:Cp() * P * OpenOrError * scoped(aps * CloseOrError) * context:Cp() / make_prob_no_cond
    end

    -- With infix "|" the delimiter collides with the operator: the rule
    -- is that the LAST "|" at parenthesis depth zero inside P(...) is
    -- the evidence separator while every earlier (or parenthesised) bar
    -- is the conditional operator.  Prescan the interior textually —
    -- skipping "||" and anything inside "()" or "[]" — then parse both
    -- sides with the full phi grammar via the sub-matcher in
    -- phi_sub_holder[1] (filled once the combined grammar exists; the
    -- holder is consulted at match time, never before).
    local function only_space(subject, from, to)
        return subject:sub(from, to - 1):match("^%s*$") ~= nil
    end

    -- the interior parses under the P scope via the sub-matcher — the
    -- scope cannot wrap the Cmt's inner lpeg.match calls, so it is
    -- pushed and popped by hand
    local function with_p_env(fn)
        local ctx = parsing_context.get_current()
        if ctx then
            ctx:push_env{slot = "bool", owner = "P", in_p = true}
        end
        local a, b = fn()
        if ctx then ctx:pop_env() end
        return a, b
    end

    local function parse_prob_interior(subject, pos)
        local depth, bdepth = 0, 0
        local last_bar, close_pos = nil, nil
        local i = pos
        while true do
            local c = subject:sub(i, i)
            if c == "" then
                -- unclosed: run phi once so its expectation labels land
                -- at the failure position; if phi reads to the end only
                -- the ")" or the evidence "|" is missing, so offer both
                local left_ast, phi_end = with_p_env(function()
                    return lpeg.match(phi_sub_holder[1], subject, pos)
                end)
                if phi_end and phi_end > #subject then
                    lpeg.match(context:Label("expected_rparen"), subject, phi_end)
                    lpeg.match(context:Label("expected_bar"), subject, phi_end)
                    lpeg.match(parsing_context.Suggest(lpeg.Cc(left_ast),
                        function(after)
                            return {kind = "ops", symbols = {")", "|"},
                                    gate = "probarg", after = after}
                        end), subject, phi_end)
                end
                return nil
            end
            if depth == 0 and bdepth == 0 and c == ")" then
                close_pos = i
                break
            end
            if c == "(" then depth = depth + 1
            elseif c == ")" then depth = depth - 1
            elseif c == "[" then bdepth = bdepth + 1
            elseif c == "]" then bdepth = bdepth - 1
            elseif c == "|" and depth == 0 and bdepth == 0 then
                if subject:sub(i + 1, i + 1) == "|" then
                    i = i + 1  -- "||" is logical or, never a separator
                else
                    last_bar = i
                end
            end
            i = i + 1
        end
        if last_bar then
            -- journal the evidence bar the prescan consumed: the
            -- operand-chain walk needs it to step past the query side
            local ctx = parsing_context.get_current()
            if ctx then
                ctx:note{kind = "pbar", from = last_bar,
                         to = last_bar + 1, owner = "P"}
            end
        end

        local phi_sub = phi_sub_holder[1]
        -- bound each side by truncating the subject at the separator /
        -- closing paren: phi would otherwise greedily read a top-level
        -- "|" as its own conditional operator.  The truncated string
        -- shares the original prefix, so ast positions stay real.
        local left_ast, left_end = with_p_env(function()
            return lpeg.match(phi_sub,
                subject:sub(1, (last_bar or close_pos) - 1), pos)
        end)
        if not left_ast or not only_space(subject, left_end, last_bar or close_pos) then
            return nil
        end
        if not last_bar then
            return close_pos, {left_ast}
        end
        local right_ast, right_end = with_p_env(function()
            return lpeg.match(phi_sub,
                subject:sub(1, close_pos - 1), last_bar + 1)
        end)
        if not right_ast or not only_space(subject, right_end, close_pos) then
            return nil
        end
        return close_pos, {left_ast, right_ast}
    end

    local function dispatch(pos_from, parts, pos_to)
        return make_prob(pos_from, parts[1], parts[2], pos_to)
    end

    return context:Cp() * P * OpenOrError
        * lpeg.Cmt(lpeg.P(true), function(subject, pos)
            return parse_prob_interior(subject, pos)
        end)
        * CloseOrError * context:Cp() / dispatch
end

return make_parser
