-- check https://codeberg.org/leso-kn/libwasmoon

local util = require "lib.util"
local make_context = require "lib.parsing_context"
local make_positional = require "lib.positional"
local features = require "lib.features"
local lpeg = require "lpeg"
local make_bn = require "bayesian_network.bayesian_network"

local function parse_to_ast(context)
   local input = context.input

   -- Lexical Elements
   local Space = lpeg.S(" \n\t")^0
   local SpaceF = lpeg.S(" \n\t")^1
   local Natural = context:Ci() * lpeg.C(lpeg.R("09")^1) * context:Ci() / tonumber * Space
   local Real = context:Ci() * (lpeg.P"-"^-1 * lpeg.R("09")^1 * ("." * lpeg.R("09")^1)^-1 * ((lpeg.S("eE") * lpeg.S("-+")^-1 * lpeg.R("09")^1)^-1)) * context:Ci() / tonumber * Space
   local Open = context:Ci() * "(" * context:Ci() * Space
   local Close = context:Ci() * ")" * context:Ci() * Space
   local LBrace = context:Ci() * "{" * context:Ci() * Space
   local RBrace = context:Ci() * "}" * context:Ci() * Space
   local LBrack = context:Ci() * "[" * context:Ci() * Space
   local RBrack = context:Ci() * "]" * context:Ci() * Space
   local Network = context:Ci() * "network" * context:Ci() * SpaceF
   local Unknown = context:Ci() * "unknown" * context:Ci() * Space
   local Identifier = context:Ci() * lpeg.C((lpeg.R"az" + lpeg.R"AZ" + "_" + lpeg.R"09") * (lpeg.R"az" + lpeg.R"AZ" + "_" + lpeg.R"09")^0) * context:Ci() * Space
   local VariableKW = context:Ci() * "variable" * context:Ci() * SpaceF
   local ProbabilityKW = context:Ci() * "probability" * context:Ci() * Space
   local Discrete = context:Ci() * "discrete" * context:Ci() * Space
   local TypeKW = context:Ci() * "type" * context:Ci() * SpaceF
   local Komma = context:Ci() * "," * context:Ci() * Space
   local Semicolon = context:Ci() * ";" * context:Ci() * Space
   local CondKW = context:Ci() * "|" * context:Ci() * Space
   local TableKW = context:Ci() * "table" * context:Ci() * SpaceF

   local function new_list(a)
      local result = {}
      table.insert(result, a)
      return result
   end

   local function insert_to_list(listt, a)
      table.insert(listt, a)
      return listt
   end

   local function new_variable(pos_from, name, num_entries, v, pos_to)
      pos_to = pos_to - 1
      local positional = make_positional(context.input, pos_from, pos_to)
      return {type="variable", variable=name, values=v, num_entries=num_entries, positional=positional}
   end

   local function make_probability_header_data(variable, dependents)
      if not dependents then
         dependents = {}
      end
      return {variable=variable, dependents=dependents}
   end

   local function make_probability_base(pos_from, header, body, pos_to)
      pos_to = pos_to - 1
      local positional = make_positional(context.input, pos_from, pos_to)
      return {type="probability_base", header=header, body=body, positional=positional}
   end

   local function make_probability_body_entry(values, probabilities)
      return {values=values, probabilities=probabilities}
   end

   local function make_probability(pos_from, header, body, pos_to)
      pos_to = pos_to - 1
      local positional = make_positional(context.input, pos_from, pos_to)
      return {type="probability", header=header, body=body, positional=positional}
   end

   local IdentifierList = (Identifier / new_list) * (Komma * Identifier % insert_to_list)^0
   local RealList = (Real / new_list) * (Komma * Real % insert_to_list)^0
   local VariableType = TypeKW * Discrete * LBrack * Natural * RBrack
   local VariableValues = LBrace * IdentifierList * RBrace * Semicolon
   local Variable = context:Cp() * VariableKW * Identifier * LBrace * VariableType * VariableValues * RBrace * context:Cp() / new_variable

   local ProbabilityBaseHeader = ProbabilityKW * Open * Identifier * Close / make_probability_header_data
   local ProbabilityBaseBody = LBrace * TableKW * RealList * Semicolon * RBrace
   local ProbabilityBase = context:Cp() * ProbabilityBaseHeader * ProbabilityBaseBody * context:Cp() / make_probability_base

   local ProbabilityTableHeader = ProbabilityKW * Open * Identifier * CondKW * IdentifierList * Close / make_probability_header_data
   local ProbabilityTableBodyEntry = Open * IdentifierList * Close * RealList * Semicolon / make_probability_body_entry
   local ProbabilityTableBody = LBrace * (ProbabilityTableBodyEntry / new_list) * (ProbabilityTableBodyEntry % insert_to_list)^0 * RBrace
   local ProbabilityTable = context:Cp() * ProbabilityTableHeader * ProbabilityTableBody * context:Cp() / make_probability
   local Probability = ProbabilityBase + ProbabilityTable

   local BN_Header = Network * Unknown * LBrace * RBrace
   local BN_Body = context:Ci() * ((Variable + Probability) / new_list) * ((Variable + Probability) % insert_to_list)^0

   local BN = BN_Header * BN_Body

   return lpeg.match(Space * BN * -1, input)
end

local function ast_to_variables(parameters)
   local m = parameters.m
   local bn = parameters.bn
   local variables_prob_entries_left = parameters.variables_prob_entries_left
   local variables_seen = parameters.variables_seen
   for _,entry in ipairs(m) do
      if entry.type == "variable" then
         assert(entry.num_entries == #entry.values,
                 {key="variable_num_values_incorrect",
                  parameters={variable=entry.variable, expected=entry.num_entries, actual=#entry.values},
                  positional=entry.positional})
         local values = {}
         for _,value in ipairs(entry.values) do
            assert(not values[value],
                    {key="duplicate_value",
                     parameters={variable=entry.variable, value=value},
                     positional=entry.positional})
            values[value] = true
         end
         -- a BIF domain has no string/number distinction: under the
         -- "numval" feature a domain whose tokens are ALL decimal
         -- numbers is taken as real-valued, while a mixed or
         -- non-numeric domain stays a string domain (no node may mix
         -- the two kinds; without the flag nothing changes)
         local fset = parameters.options
            and features.parse(parameters.options:get("features")) or {}
         local outc = entry.values
         if fset.numval then
            local converted, seen_num, numeric = {}, {}, true
            for i,value in ipairs(entry.values) do
               -- BIF identifiers cannot contain ".", "-" or "+", so a
               -- plain tonumber covers exactly what the format can
               -- express (integers and exponent forms)
               local n = tonumber(value)
               if not n or n ~= n or n == math.huge or n == -math.huge then
                  numeric = false
                  break
               end
               assert(not seen_num[n],
                       {key="duplicate_value",
                        parameters={variable=entry.variable, value=value},
                        positional=entry.positional})
               seen_num[n] = true
               converted[i] = n
            end
            if numeric then outc = converted end
         end
         bn:set_values(entry.variable, outc)
         variables_prob_entries_left[entry.variable] = true
         assert(not variables_seen[entry.variable],
                 {key="variable_defined_twice",
                  parameters={variable=entry.variable},
                  positional=entry.positional})
         variables_seen[entry.variable] = true
      end
   end
end

local function ast_to_probability_base(parameters)
   local m = parameters.m
   local bn = parameters.bn
   local variables_seen = parameters.variables_seen
   local prob_entries_seen = parameters.prob_entries_seen
   local variables_prob_entries_left = parameters.variables_prob_entries_left
   local options = parameters.options
   local tolerance = 1.0E-6
   if options then
      tolerance = options:get("probability_tolerance") or tolerance
   end
   for _,entry in ipairs(m) do
      if entry.type == "probability_base" then
         local variable = entry.header.variable
         assert(variables_seen[variable],
                 {key="probability_for_undefined_variable",
                  parameters={variable=variable},
                  positional=entry.positional})
         assert(not prob_entries_seen[variable],
                 {key="probability_for_variable_defined_twice",
                  parameters={variable=variable},
                  positional=entry.positional})
         prob_entries_seen[variable] = true
         variables_prob_entries_left[variable] = nil
         local values = bn:get_values(variable)
         assert(values)
         assert(#values == #entry.body,
                 {key="probability_count_mismatch",
                  parameters={variable=variable, expected=#values, actual=#entry.body},
                  positional=entry.positional})
         local probabilities = {}
         local sum = 0
         for i,value in ipairs(values) do
            probabilities[value] = entry.body[i]
            sum = sum + entry.body[i]
         end
         assert(math.abs(sum - 1.0) < tolerance,
                 {key="probability_sum_incorrect",
                  parameters={variable=variable, sum=sum},
                  positional=entry.positional})
         bn:set_probabilies(variable, {}, probabilities)
      end
   end
end

local function compute_expected_entries(bn, dependents)
   local expected_entries = {}
   local expected_num_entries = 1
   for _,dependent in ipairs(dependents) do
      local dependent_values = bn:get_values(dependent)
      expected_num_entries = expected_num_entries * #dependent_values
   end
   for value_number=0,expected_num_entries-1 do
      local rest = value_number
      local entry = {}
      for _,dependent in ipairs(dependents) do
         local dependent_values = bn:get_values(dependent)
         local dependent_value_number = math.floor(rest % #dependent_values) + 1
         rest = math.floor(rest / #dependent_values)
         local dependent_value = dependent_values[dependent_value_number]
         table.insert(entry, dependent_value)
      end
      entry = table.concat(entry, ",")
      table.insert(expected_entries, entry)
   end
   return expected_entries
end

local function ast_to_probability(parameters)
   local m = parameters.m
   local bn = parameters.bn
   local prob_entries_seen = parameters.prob_entries_seen
   local variables_seen = parameters.variables_seen
   local variables_prob_entries_left = parameters.variables_prob_entries_left
   local options = parameters.options
   local tolerance = 1.0E-6
   if options then
      tolerance = options:get("probability_tolerance") or tolerance
   end
   for _,entry in ipairs(m) do
      if entry.type == "probability" then
         local variable = entry.header.variable
         assert(variables_seen[variable],
                 {key="probability_for_undefined_variable",
                  parameters={variable=variable},
                  positional=entry.positional})
         assert(not prob_entries_seen[variable],
                 {key="probability_for_variable_defined_twice",
                  parameters={variable=variable},
                  positional=entry.positional})
         prob_entries_seen[variable] = true
         local variable_values = bn:get_values(variable)
         assert(variable_values)
         variables_prob_entries_left[variable] = nil
         local dependents = entry.header.dependents
         local dependents_values = {}
         for _,dependent in ipairs(dependents) do
            local dependent_values = bn:get_values(dependent)
            assert(dependent_values,
                    {key="undefined_dependent_variable",
                     parameters={variable=variable, dependent=dependent},
                     positional=entry.positional})
            -- a row token is looked up by its written form and resolves
            -- to the domain value — numeric domains (see the "numval"
            -- coercion in ast_to_variables) yield the number itself
            local dep_map = {}
            for _,v in ipairs(dependent_values) do dep_map[tostring(v)] = v end
            dependents_values[dependent] = dep_map
         end
         local entries = {}
         for _,body_entry in ipairs(entry.body) do
            local row = {}
            local row_for = {}
            assert(#body_entry.values == #dependents,
                    {key="condition_length_mismatch",
                     parameters={variable=variable},
                     positional=entry.positional})
            for i,dependent in ipairs(dependents) do
               local value = dependents_values[dependent][body_entry.values[i]]
               assert(value ~= nil,
                       {key="invalid_dependent_value",
                        parameters={variable=variable, dependent=dependent, value=body_entry.values[i]},
                        positional=entry.positional})
               row[dependent] = value
               table.insert(row_for, value)
            end
            local row_string = table.concat(row_for, ",")
            assert(not entries[row_string],
                    {key="duplicate_probability_row",
                     parameters={variable=variable, row=row_string},
                     positional=entry.positional})
            entries[row_string] = true

            local probabilities = {}
            local sum = 0
            assert(#body_entry.probabilities == #variable_values,
                    {key="probability_count_mismatch",
                     parameters={variable=variable, expected=#variable_values, actual=#body_entry.probabilities},
                     positional=entry.positional})
            for i,value in ipairs(variable_values) do
               local probability = body_entry.probabilities[i]
               probabilities[value] = probability
               sum = sum + probability
            end
            assert(math.abs(sum - 1.0) < tolerance,
                    {key="probability_sum_incorrect",
                     parameters={variable=variable, sum=sum},
                     positional=entry.positional})
            bn:set_probabilies(variable, row, probabilities)
         end
         local expected_entries = compute_expected_entries(bn, dependents)
         for _,expected_row in ipairs(expected_entries) do
            assert(entries[expected_row],
                    {key="missing_probability_row",
                     parameters={variable=variable, row=expected_row},
                     positional=entry.positional})
         end
      end
   end
   if util.count_entries(variables_prob_entries_left) > 0 then
      local missing = {}
      for k,_ in pairs(variables_prob_entries_left) do table.insert(missing, k) end
      error({key="missing_probability_definitions", parameters={variables=table.concat(missing, ", ")}})
   end
end

local function ast_to_bn(m, options)
   local bn = make_bn()
   local parameters = {}
   local variables_prob_entries_left = {}
   local variables_seen = {}
   local prob_entries_seen = {}
   parameters.m = m
   parameters.bn = bn
   parameters.options = options
   parameters.variables_prob_entries_left = variables_prob_entries_left
   parameters.variables_seen = variables_seen
   parameters.prob_entries_seen = prob_entries_seen
   ast_to_variables(parameters)
   ast_to_probability_base(parameters)
   ast_to_probability(parameters)
   return bn
end

local function parse(input, options)
   assert(type(input) == "string")
   local context = make_context(input)
   local m = parse_to_ast(context)
   if m then
      m = ast_to_bn(m, options)
   end
   if not m then
      error({key="parsing_error", positional=make_positional(input, context:get_last_position())})
   end
   return m
end

return parse