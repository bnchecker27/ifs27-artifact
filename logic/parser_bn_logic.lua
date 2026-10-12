local logic = require "logic.logic"
local lpeg = require "lpeg"
local operator_utils = require "logic.operators"
local util = require "lib.util"
local lpeg_util = require "lib.lpeg_util"
local features_module = require "lib.features"
local parser_formula = require "logic.parser_formula"
local parser_identifier = require "logic.parser_identifier"
local parser_real = require "logic.parser_real"
local make_positional = require "lib.positional"
local infl = require "logic.parser_infl"
local idp = require "logic.parser_idp"
local box = require "logic.parser_box"
local map = require "logic.parser_map"
local mpe = require "logic.parser_mpe"
local prob = require "logic.parser_prob_quantifier"
local make_parser_modify_probability = require "logic.parser_modify_probability"
local parsing_context = require "lib.parsing_context"

local compare_op_map = operator_utils.make_symbol_to_operator_map(operator_utils.compare_operators)

local Space = lpeg.S(" \n\t")^0

-- a comparison operator is a compare-class separator: the resolver's
-- compare_tail finds the claim's "l op r" boundary from the journal,
-- and the slot after it is a right-operand ("compare") slot
local function cmp_sym(sym_patt, sym)
   return lpeg_util.sep_note(lpeg.C(sym_patt), "csep",
      function(_, s) return {cls = "cmp", nslot = "compare", sym = s} end)
      * Space / sym
end
local Less = cmp_sym(lpeg.P"<", "<")
local LessOrEquals = cmp_sym(lpeg.P"<=" + "≤", "≤")
local Equals = cmp_sym(lpeg.P"=", "=")
local GreaterOrEquals = cmp_sym(lpeg.P">=" + "≥", "≥")
local Greater = cmp_sym(lpeg.P">", ">")

local function get_compare_operator(op)
   return compare_op_map[op]
end


local function make_compare(context)
    local ops = {kind = "ops", symbols = {"=", "≤", "≥", "<", ">"},
                 needs = "term"}
    return ((LessOrEquals + GreaterOrEquals + Less + Greater + Equals)
            + context:Label("expected_compare")
            + parsing_context.Suggest(
                lpeg.Cb("sug_after") + lpeg.Cc(nil),
                function(after)
                    return {kind = "ops", symbols = ops.symbols,
                            needs = "term", after = after}
                end))
           / get_compare_operator
end

local function make_variable_compare_parser(context, phi_var, feature_set, varterm)
   local function make_cmp(pos_from, left, op, right, pos_to)
      pos_to = pos_to - 1
      local positional = make_positional(context.input, pos_from, pos_to)
      return logic.make_binary_operator(left, right, op, positional)
   end

   -- comparison operands take literal outcome names, so the reserved
   -- literals stay legal here: "GOAL_2 = true" is the andes domain
   -- spelling.  A bare "true" in a claim position is still rejected —
   -- this looser alternative only lives inside the compare operand
   local parserIdentifier = parser_identifier(context, true)
   -- a parenthesised operand lets "(X | C) = x" compare a conditional
   -- term against an outcome; the group is transparent — it yields the
   -- inner node itself, so "(X) = x" stays a plain comparison.  Its
   -- interior is a fresh "any" operand even under a compare slot —
   -- "A = (…)" opens a self-contained formula — so the scope clears
   -- the compare slot and the enclosing paren's owner
   local group = lpeg_util.Open
               * lpeg_util.sug_scope(phi_var, {
                    owner = false,
                    in_p = false,
                    slot = function(e)
                        if e and e.slot == "compare" then return "any" end
                    end})
               * (lpeg_util.labeled(lpeg_util.Close, "expected_rparen", {kw = ")"}))
   -- suggestion categories per operand alternative: a failure inside the
   -- operand slot reports which operand kinds were viable there; the
   -- mark journals each completed operand's end so the resolver's
   -- operand-chain walk sees the atoms
   local operand = lpeg_util.suggestable(parserIdentifier, {cat = "ident", mark = "atom"})
                 + lpeg_util.suggestable(group, {cat = "paren", mark = "expr"})
   if feature_set.numval then
      -- "X = 0.5" / "X < 0.5": a numeric literal may compare against a
      -- real-valued variable
      operand = operand + lpeg_util.suggestable(parser_real(context), {cat = "number", mark = "atom"})
   end
   -- the operand node becomes the "sug_after" value the continuation
   -- and rhs annotations read (track binds it at this rule's top level,
   -- so it stays visible to the back references below — a group nested
   -- inside a full capture would be invisible to them)
   operand = lpeg_util.track(operand)
   -- suggestion annotation: a rhs failure reads "sug_after" — still the
   -- left operand's node at that point — and reports its variable so the
   -- suggester can offer that variable's outcomes.  A non-identifier
   -- left operand falls back to a generic operand category.
   local function rhs_suggest(left)
      if type(left) == "table" and type(left.get_identifier) == "function" then
         local ok, name = pcall(function() return left:get_identifier() end)
         if ok and type(name) == "string" then
            return {kind = "outcome-of", var = name}
         end
      end
      return {kind = "operand"}
   end
   -- the right operand sits in a "compare" slot: payloads registered
   -- inside it — including the fallback suggestion itself — and its
   -- operand-end note carry the stamp
   local second_operand = lpeg_util.labeled(
      lpeg_util.sug_scope(
         lpeg_util.suggestable_after(operand, rhs_suggest),
         {slot = "compare"}),
      "expected_identifier")
   local Compare = make_compare(context)

   local cmp = context:Cp()
             * operand
             * Compare * second_operand * context:Cp() / make_cmp

    return cmp
end

-- a subtree that references no model variable: a numeric constant or an
-- arithmetic expression over constants (an intervened-on constant is
-- still constant, so a nested modify_probability keeps purity)
local function is_pure_numeric(ast)
   if not ast or type(ast) ~= "table" then return false end
   local t = ast:get_type()
   if t == "value" then return true end
   if t ~= "operator" then return false end
   local op = ast:get_operator_name()
   if op == "times" or op == "minus" or op == "plus" or op == "divide" then
      for i = 1, ast:get_num_children() do
         if not is_pure_numeric(ast:get_child(i)) then return false end
      end
      return true
   end
   if op == "modify_probability" then
      local inner = ast.get_child_or_nil and ast:get_child_or_nil(1)
      return inner ~= nil and is_pure_numeric(inner)
   end
   return false
end

local function make_value_compare_parser(context, psi)
   -- A trailing intervention [X↦v] directly after a pure-numeric operand
   -- intervenes on the whole comparison, not on the constant: "P(A) >=
   -- 0.995 [X↦v]" means "(P(A) >= 0.995) [X↦v]".  Without the hoist, the
   -- psi postfix layer would bind [X↦v] to the number itself — a semantic
   -- no-op that silently loses the intervention.  (An operand that
   -- references the model, e.g. P(X)[Y↦y], keeps the postfix.)
   local function take_modify(operand)
      if operand:get_type() == "operator"
         and operand:get_operator_name() == "modify_probability"
         and is_pure_numeric(operand:get_child(1)) then
         return operand:get_operator(), operand:get_child(1)
      end
      return nil, operand
   end
   local function make_cmp(pos_from, left, op, right, pos_to)
      pos_to = pos_to - 1
      local lmod, rmod
      lmod, left = take_modify(left)
      rmod, right = take_modify(right)
      local cmp_pos = make_positional(context.input, pos_from,
         right:get_positional() and right:get_positional().to or pos_to)
      local node = logic.make_binary_operator(left, right, op, cmp_pos)
      local outer_pos = make_positional(context.input, pos_from, pos_to)
      if rmod then node = rmod.make_operator(node, outer_pos) end
      if lmod then node = lmod.make_operator(node, outer_pos) end
      return node
   end

   -- psi subsumes bare numbers (they are psi atoms), so a plain psi
   -- operand also covers 0.5 / 0.5-0.3 etc.  Trying parserReal first
   -- would stop `0.5-0.3` at `0.5` and lose the arithmetic tail.
   local parser_operands = lpeg_util.labeled(psi, "expected_value",
      {cat = "value"})
   -- the right operand sits in a "compare" slot like the variable
   -- compare's: its operand-end note and any payloads inside carry the
   -- stamp the bool-chain walk keys on
   local parser_rhs = lpeg_util.labeled(
      lpeg_util.sug_scope(psi, {slot = "compare"}),
      "expected_value", {cat = "value"})
   local Compare = make_compare(context)

   local cmp = context:Cp() * parser_operands * Compare * parser_rhs * context:Cp() / make_cmp
    return cmp
end



local function build_grammar(context, feature_set)
    local phi_var = lpeg.V("phi")
    local psi_var = lpeg.V("psi")
    -- the paper's language has no variable-producing term
    -- constructors (DIST/RENAME/MUX/PDIST), so the varterm category is
    -- empty
    local varterm = lpeg.P(false)
    local variable_cmp = make_variable_compare_parser(context, phi_var, feature_set, varterm)
    local value_compare = make_value_compare_parser(context, psi_var)
    local operators_phi = util.append_arrays(operator_utils.logical_operators, operator_utils.modify_probability)
    -- all four scalar operators are builtin (the former "arith" gate
    -- only ever held + and ÷ — an asymmetry with no syntactic reason)
    local operators_psi = util.append_arrays(operator_utils.arithmetic_operators, operator_utils.modify_probability)
    local map_parser = map(phi_var, context)
    local mpe_parser = mpe(phi_var, context)
    local idp_parser = idp(context)
    local infl_parser = infl(context)
    local box_parser = box(context)
    -- the box placeholder is valid wherever a formula (phi) or a numeric
    -- operand (psi) is expected; semantic validation rejects it later.
    -- Bare numeric constants are psi atoms, so `0.5`, `0.5-0.3` and
    -- `P(X=x)*0.5` are all valid (top-level) formulae.  A bare
    -- identifier is a complete phi formula (the variable's marginal is
    -- the query) — it must come LAST: ordered choice commits, so the
    -- compare and keyword parsers get "Grade = High", "MAP(...)" and
    -- "P(...)" before a lone identifier can claim their first word.
    -- suggestion annotations: each alternative registers what it would
    -- have offered had the parse died here — a failed atom position
    -- reports the offerable keyword/category set for free
    local aps_phi = context:Label("expected_phi")
                  + lpeg_util.suggestable(variable_cmp, {cat = "compare"})
                  + lpeg_util.suggestable(value_compare, {cat = "value-compare"})
                  + lpeg_util.suggestable(map_parser, {kw = "MAP(", mark = "kwexpr", mkw = "MAP"})
                  + lpeg_util.suggestable(mpe_parser, {kw = "MPE(", mark = "kwexpr", mkw = "MPE"})
                  + lpeg_util.suggestable(idp_parser, {kw = "IDP(", mark = "kwexpr", mkw = "IDP"})
                  + lpeg_util.suggestable(infl_parser, {kw = "INFL(", mark = "kwexpr", mkw = "INFL"})
                  + lpeg_util.suggestable(box_parser, {cat = "box"})
                  + lpeg_util.suggestable(parser_identifier(context), {cat = "ident", mark = "atom"})

    local operator_phi_symbol_parsers = {}
    local operator_psi_symbol_parsers = {}
    do
        local parser_modify_probability = make_parser_modify_probability(context)
        operator_phi_symbol_parsers["modify_probability"] = parser_modify_probability
        operator_psi_symbol_parsers["modify_probability"] = parser_modify_probability
    end
    local parser_phi_parameters = {
          name="phi",
          operators=operators_phi,
          aps=aps_phi,
          operator_symbol_parsers=operator_phi_symbol_parsers,
          infix_label="expected_logical_operator",
          postfix_label="expected_lbrack",
          context=context
    }
    local parser_phi = parser_formula(parser_phi_parameters)

    -- sub-matcher for the P(...) interior prescan: parses a full phi
    -- (with the infix "|" layer) at an arbitrary offset and yields the
    -- ast plus the position after the match, so the prob parser can
    -- split query/evidence at the last top-level bar.  It needs every
    -- rule of the combined grammar (phi references psi through value
    -- comparisons), so it is compiled only after the merge below — the
    -- holder is filled before the grammar is ever matched.
    local phi_sub_holder = {}
    local prob_parser = prob(phi_var, context, feature_set, phi_sub_holder)

    local aps_psi = context:Label("expected_psi")
                  + lpeg_util.suggestable(parser_real(context), {cat = "number", mark = "atom"})
                  + lpeg_util.suggestable(prob_parser, {kw = "P(", mark = "kwexpr", mkw = "P"})
                  + lpeg_util.suggestable(box_parser, {cat = "box"})
    local parser_psi_parameters = {
          name="psi",
          operators=operators_psi,
          aps=aps_psi,
          operator_symbol_parsers=operator_psi_symbol_parsers,
          infix_label="expected_arithmetic_operator",
          postfix_label="expected_lbrack",
          context=context
    }
    local parser_psi = parser_formula(parser_psi_parameters)

    local grammar = {}
    for k, v in pairs(parser_phi) do grammar[k] = v end
    for k, v in pairs(parser_psi) do grammar[k] = v end
    -- Each alternative must consume the input completely; ordered choice
    -- is committed, so "phi * eof + psi * eof" is required instead of
    -- "(phi + psi) * eof": otherwise a leading box (or parenthesised
    -- box), a valid phi atom, would commit the input to phi and a
    -- following arithmetic operator could never reach psi — "□ − 0"
    -- failed to parse while "0 − □" worked.
    local not_eof = lpeg_util.labeled(-lpeg.P(1), "expected_eof",
        {kind = "eof"})
    -- the root operands sit in the "any" slot: every payload and
    -- operand-end note at top level carries the stamp
    grammar[1] = lpeg_util.sug_scope(
        lpeg.V("phi") * not_eof + lpeg.V("psi") * not_eof,
        {slot = "any"})
    return lpeg.P(grammar)
end

-- The built grammar is input-independent — its patterns read the shared
-- "current" parsing context at match time — so it is cached per feature
-- set and the context re-armed per call instead of rebuilding the whole
-- grammar (~60% of a parse's cost was construction).
local grammar_cache = {}
local function parse(input, features)
   assert(type(input) == "string")
   local fs = features_module.parse(features)
   -- callers pass an already-parsed set table (fresh each call), so the
   -- cache key is the canonical sorted list of enabled feature names
   local names = {}
   for name in pairs(fs) do names[#names + 1] = name end
   table.sort(names)
   local key = table.concat(names, ",")
   local entry = grammar_cache[key]
   if not entry then
      local context = parsing_context(input)
      entry = {context = context,
               grammar = build_grammar(context, fs)}
      grammar_cache[key] = entry
   end
   local context = entry.context
   context:reset(input)
   parsing_context.set_current(context)
   local m = lpeg.match(entry.grammar, input, 1)
   if not m then
      error({key="parsing_error",
             expected=context:get_expected(),
             suggest=context:get_suggest(),
             order=context:get_order(),
             notes=context:get_notes(),
             positional=make_positional(input, context:get_last_position())})
   end
   return m
end

return parse
