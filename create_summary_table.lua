-- Script to generate LaTeX tables from experiment results
-- Reads: experiments.csv, chosen.csv, explanations.csv, results.csv
-- Generates: LaTeX table fragments and itemize descriptions

local SEED = 42
math.randomseed(SEED)

-- Read CSV files (simple parser, auto-detect delimiter)
local function read_csv(filename)
    local data = {}
    local file = io.open('overleaf/experiments/' .. filename, 'r')
    if not file then
        print("ERROR: Could not open overleaf/experiments/" .. filename)
        return data
    end
    
    local header = file:read('*l')
    if not header then return data end
    header = header:gsub("\r", "")
    
    -- Detect delimiter (semicolon or comma)
    local delimiter = header:find(';') and ';' or ','
    
    -- Parse header, handling quoted fields
    local fields = {}
    local field = ""
    local in_quotes = false
    for c in header:gmatch('.') do
        if c == '"' then
            in_quotes = not in_quotes
        elseif c == delimiter and not in_quotes then
            table.insert(fields, field)
            field = ""
        else
            field = field .. c
        end
    end
    table.insert(fields, field)
    
    -- Parse data rows
    for line in file:lines() do
        line = line:gsub("\r", "")
        if line:match('%S') then
            local row = {}
            local value = ""
            in_quotes = false
            local i = 1
            for c in line:gmatch('.') do
                if c == '"' then
                    in_quotes = not in_quotes
                elseif c == delimiter and not in_quotes then
                    if fields[i] then
                        row[fields[i]] = value
                    end
                    value = ""
                    i = i + 1
                else
                    value = value .. c
                end
            end
            if fields[i] then
                row[fields[i]] = value
            end
            table.insert(data, row)
        end
    end
    
    file:close()
    return data
end

-- Load data
local experiments = read_csv('experiments.csv')
local chosen_data = read_csv('chosen.csv')
local explanations = read_csv('explanations.csv')
local results_data = read_csv('results.csv')

-- Build lookup tables
local experiments_by_name = {}
for _, exp in ipairs(experiments) do
    experiments_by_name[exp.name] = exp
end

local results_by_name = {}
for _, res in ipairs(results_data) do
    if not results_by_name[res.name] then
        results_by_name[res.name] = {}
    end
    if res.engine == "var_elim" then
        results_by_name[res.name].var_elim_result = res.result
        results_by_name[res.name].var_elim_time = res.runtime
    elseif res.engine == "sampling" then
        results_by_name[res.name].sampling_result = res.result
        results_by_name[res.name].sampling_time = res.runtime
    end
end

local explanations_by_name = {}
for _, expl in ipairs(explanations) do
    explanations_by_name[expl.name] = expl
end

-- Build chosen experiments set (preserve order from experiments.csv)
local chosen_experiments = {}
local chosen_order = {}
for _, exp in ipairs(experiments) do
    if chosen_experiments[exp.name] == nil then
        for _, row in ipairs(chosen_data) do
            if row.name == exp.name then
                chosen_experiments[exp.name] = true
                table.insert(chosen_order, exp.name)
                break
            end
        end
    end
end

-- Model information
local MODEL_VAR_COUNTS = {
    win95 = 76,
    munin = 1041,
    insurance = 27,
    andes = 223,
    pigs = 441,
    grades = 5,
    link = 724,
    pathfinder = 109
}

local MODEL_DOMAINS = {
    win95 = "Printer troubleshooting",
    munin = "Medical diagnosis assist.",
    insurance = "Car insurance",
    andes = "Space shuttle (ANDES)",
    pigs = "Genetic analysis",
    grades = "Academic grades",
    link = "Genetic analysis",
    pathfinder = "Pathology diagnosis"
}

-- Generate abbreviation by removing case study prefix (e.g., "win95_map" -> "map")
local function get_abbreviation(exp_name)
    -- Find the first underscore and remove everything before and including it
    local first_underscore = exp_name:find("_")
    if first_underscore then
        return exp_name:sub(first_underscore + 1)
    end
    return exp_name
end

-- BayesL-style category labels for property descriptions
local function has_finite_verb(s)
    local lower = " " .. s:lower() .. " "
    local verbs = {" is ", " are ", " was ", " were ", " has ", " have ", " had ", " equals ", " equal ", " denotes ", " indicates ", " gives ", " yields ", " shows ", " exceeds ", " exceed ", " remains ", " depend ", " depends ", " suffice ", " suffices ", " found ", " suggests ", " reveals ", " confirms ", " consistent ", " independent ", " dependent ", " inconsistent "}
    for _, v in ipairs(verbs) do
        if lower:find(v, 1, true) then
            return true
        end
    end
    return false
end

local function answer_to_statement(answer)
    local s = (answer or "")
    s = s:gsub("^%s+", ""):gsub("%s+$", "")
    s = s:gsub("%.$", "")
    -- Remove leading Yes, / No, answer prefixes
    local lower = s:lower()
    if lower:sub(1, 5) == "yes, " then
        s = s:sub(6)
    elseif lower:sub(1, 4) == "no, " then
        s = s:sub(5)
    end
    s = s:gsub("^%s+", "")
    if not has_finite_verb(s) then
        if #s > 0 then
            s = s:sub(1,1):lower() .. s:sub(2)
        end
        s = "The result is " .. s
    else
        if #s > 0 then
            s = s:sub(1,1):upper() .. s:sub(2)
        end
    end
    if s:sub(-1) ~= "." then
        s = s .. "."
    end
    return s
end

local function is_combined_verification(property)
    local depth = 0
    local i = 1
    local n = #property
    while i <= n do
        local c = property:sub(i, i)
        if c == "(" then
            depth = depth + 1
            i = i + 1
        elseif c == ")" then
            depth = depth - 1
            i = i + 1
        elseif c == "\226" and (property:sub(i+1, i+2) == "\136\167" or property:sub(i+1, i+2) == "\136\168") then
            if depth == 0 then
                return true
            end
            i = i + 3
        else
            i = i + 1
        end
    end
    return false
end

local function get_property_category(abbr, property)
    local a = abbr:lower()
    if a:find("^idp") or a:find("^infl") then
        return "Structural reasoning."
    elseif a:find("^map") or a:find("^mpe") then
        return "MAP and MPE."
    elseif a:find("intervention") or property:find("%[") or property:find("↦") then
        return "What-if analysis."
    elseif is_combined_verification(property) then
        return "Combined verification."
    else
        return "Marginal and conditional inference."
    end
end

-- Helper functions
local function escape_latex(str)
    if not str then return ""
    end
    -- Don't escape backslashes - assume input already has LaTeX formatting
    -- str = str:gsub("\\", "\\textbackslash{}")
    str = str:gsub("_", "\\_")
    str = str:gsub("%%", "\\%%")
    str = str:gsub("&", "\\&")
    str = str:gsub("#", "\\#")
    str = str:gsub("<", "\\textless{}")
    str = str:gsub(">", "\\textgreater{}")
    -- Don't escape braces - assume they're part of LaTeX commands
    -- str = str:gsub("{", "\\{")
    -- str = str:gsub("}", "\\}")
    str = str:gsub("~", "\\textasciitilde{}")
    str = str:gsub("%^", "\\textasciicircum{}")
    -- Escape Unicode characters
    str = str:gsub("≤", "$\\leq$")
    str = str:gsub("≥", "$\\geq$")
    str = str:gsub("↦", "$\\mapsto$")
    str = str:gsub("∧", "$\\land$")
    str = str:gsub("∨", "$\\lor$")
    str = str:gsub("¬", "$\\lnot$")
    str = str:gsub("−", "$-$")
    str = str:gsub("×", "$\\times$")
    str = str:gsub("÷", "$\\div$")
    return str
end

-- Escape only the chars that are catcode-active inside a detokenized
-- \bprint{...} argument.  Formula UTF-8 symbols stay raw so the Lua
-- highlighter can classify them; descriptions still use escape_latex.
local function escape_bprint(str)
    if not str then return ""
    end
    str = str:gsub("_", "\\_")
    str = str:gsub("%%", "\\%%")
    str = str:gsub("&", "\\&")
    str = str:gsub("#", "\\#")
    return str
end

-- Insert literal spaces at safe split points so \bprint formulas can wrap
-- (a space is breakable inside the pdflatex \texttt fallback, and the
-- lualatex formatter turns it into an allowbreak + space as well).
local function bprint_breakable(str)
    str = escape_bprint(str)
    str = str:gsub("∧", "∧ ")
    str = str:gsub("∨", "∨ ")
    str = str:gsub("→", "→ ")
    str = str:gsub("−", "− ")
    str = str:gsub(",", ", ")
    str = str:gsub("%)(%[)", ") %1")
    str = str:gsub("%](%[)", "] %1")
    str = str:gsub("(%d)(%[)", "%1 %2")
    str = str:gsub("≥", " ≥")
    str = str:gsub("≤", " ≤")
    str = str:gsub("<", " <")
    str = str:gsub(">", " >")
    return str
end

local function format_time(time_str)
    if not time_str or time_str == "" then return "N/A" end
    local num = tonumber(time_str)
    if not num then return time_str end
    if num < 1 then return "\\textless{}1" end
    return string.format("%.0f", num)
end

-- A run failed if its result is an error/crash marker (e.g. OOM kill)
local function is_failed_run(result_str)
    if not result_str then return false end
    if result_str == "Crash" then return true end
    if result_str:find("ERROR:") then return true end
    if result_str:find("Mem out") then return true end
    return false
end

-- Time column entry: mark terminated runs as "oom" instead of a runtime
local function format_time_or_failure(result_str, time_str)
    if is_failed_run(result_str) then return "\\emph{oom}" end
    return format_time(time_str)
end

local function format_result(result_str)
    if not result_str or result_str == "" then return "N/A" end
    -- Remove "Result: " prefix if present
    result_str = result_str:gsub("^Result: ", "")
    -- Trim leading/trailing whitespace
    result_str = result_str:gsub("^%s+", "")
    result_str = result_str:gsub("%s+$", "")
    -- Replace ERROR messages with "Mem Out"
    if result_str:find("ERROR:") or result_str:find("Mem out") then
        result_str = "Mem Out"
    end
    -- Round numeric results to 4 decimal places
    local num = tonumber(result_str)
    if num then
        result_str = string.format("%.4f", num)
    end
    -- Format MAP/MPE results with commas (e.g., "A=a B=b C=c" -> "A=a,B=b,C=c")
    if result_str:find("=") then
        -- Split into variable=value pairs
        local pairs = {}
        local current_pair = ""
        for token in result_str:gmatch("[^%s]+") do
            if token == "=" then
                current_pair = current_pair .. "="
            elseif current_pair:find("=") then
                -- This is the value part
                current_pair = current_pair .. token
                table.insert(pairs, current_pair)
                current_pair = ""
            else
                -- This is a variable name
                current_pair = token
            end
        end
        -- If we have more than 3 pairs, abbreviate with commas
        if #pairs > 3 then
            result_str = pairs[1] .. ",...," .. pairs[#pairs]
        else
            -- Join all pairs with commas
            result_str = table.concat(pairs, ",")
        end
    end
    -- Truncate very long results
    if #result_str > 100 then
        result_str = string.sub(result_str, 1, 100) .. "..."
    end
    -- Replace multiple spaces with single space
    result_str = result_str:gsub("%s+", " ")
    -- Don't replace = with math mode - it causes issues in tables
    -- result_str = result_str:gsub("=", "$=$")
    -- Replace < and > with text mode for table results
    result_str = result_str:gsub("<", "\\textless{}")
    result_str = result_str:gsub(">", "\\textgreater{}")
    return result_str
end

local function count_table(t)
    local count = 0
    for _ in pairs(t) do count = count + 1 end
    return count
end

-- Generate itemize descriptions
local function generate_itemize_descriptions(experiment_set, output_file, separate_files, use_full_prefix)
    local itemize_file
    
    if separate_files then
        -- Will create separate files per model
        local model_files = {}
        local model_names = {}
        for name, exp in pairs(experiments_by_name) do
            if experiment_set[name] then
                local model = exp.model
                if not model_files[model] then
                    local prefix = use_full_prefix and "property_descriptions_full_" or "property_descriptions_"
                    model_files[model] = io.open("overleaf/experiments/" .. prefix .. model .. ".tex", "w")
                    if model_files[model] then
                        local size = use_full_prefix and "\\footnotesize" or ""
                        model_files[model]:write("\\begingroup" .. size .. "\\raggedright\n")
                        model_files[model]:write("\\begin{itemize}[nosep,leftmargin=*]\n")
                    end
                    model_names[model] = {}
                end
                table.insert(model_names[model], name)
            end
        end
        
        -- Sort property names alphabetically per model
        for model, names in pairs(model_names) do
            table.sort(names, function(a, b)
                return get_abbreviation(a) < get_abbreviation(b)
            end)
        end
        
        for model, names in pairs(model_names) do
            local file = model_files[model]
            if file then
                for _, name in ipairs(names) do
                    local exp = experiments_by_name[name]
                    local expl = explanations_by_name[name]
                    if expl then
                        local abbr = get_abbreviation(name)
                        local category = get_property_category(abbr, exp.property)
                        local statement = not use_full_prefix and expl.statement and expl.statement ~= "" and expl.statement or answer_to_statement(expl.explanation or "")
                        model_files[model]:write("\\item \\prop{" .. escape_bprint(abbr) .. "}: \\emph{" .. escape_latex(category) .. "} \\bprint{" .. bprint_breakable(exp.property) .. "} " .. escape_latex(statement) .. "\n")
                    end
                end
            end
        end
        
        for model, file in pairs(model_files) do
            if file then
                file:write("\\end{itemize}\n")
                file:write("\\endgroup\n")
                file:close()
                local prefix = use_full_prefix and "property_descriptions_full_" or "property_descriptions_"
                print("Writing to overleaf/experiments/" .. prefix .. model .. ".tex")
            end
        end

    else
        itemize_file = io.open(output_file, 'w')
        if not itemize_file then
            print("ERROR: Could not open " .. output_file)
            return
        end
        
        itemize_file:write("\\begin{itemize}\n")
        
        for name, exp in pairs(experiments_by_name) do
            if experiment_set[name] then
                local expl = explanations_by_name[name]
                if expl then
                    local abbr = get_abbreviation(name)
                    local category = get_property_category(abbr, exp.property)
                    local statement = not use_full_prefix and expl.statement and expl.statement ~= "" and expl.statement or answer_to_statement(expl.explanation or "")
                    itemize_file:write("\\item \\prop{" .. escape_bprint(abbr) .. "}: \\emph{" .. escape_latex(category) .. "} \\bprint{" .. bprint_breakable(exp.property) .. "} " .. escape_latex(statement) .. "\n")
                end
            end
        end
        
        itemize_file:write("\\end{itemize}\n")
        itemize_file:close()
    end
end

-- Generate LaTeX tables
local function generate_latex_tables(experiment_set, fragment_filename, standalone_filename, use_abbreviated, include_descriptions, separate_files, order_list)
    local fragment
    
    if separate_files then
        -- Group experiments by model
        local model_groups = {}
        for name, exp in pairs(experiments_by_name) do
            if experiment_set[name] then
                local model = exp.model
                if not model_groups[model] then
                    model_groups[model] = {}
                end
                table.insert(model_groups[model], name)
            end
        end
        
        -- Create separate file for each model
        for model, exp_names in pairs(model_groups) do
            local model_filename = fragment_filename:gsub("%.tex$", "_" .. model .. ".tex")
            fragment = io.open(model_filename, 'w')
            if not fragment then
                print("ERROR: Could not open " .. model_filename .. " for writing")
                return
            end
            print("Writing to " .. model_filename)
            
            -- Sort properties alphabetically by abbreviation
            table.sort(exp_names, function(a, b)
                return get_abbreviation(a) < get_abbreviation(b)
            end)
            
            fragment:write("\\begingroup\\footnotesize\n")
            fragment:write("\\noindent\\begin{tabularx}{\\columnwidth}{@{}l Y c c@{}}\n")
            fragment:write("\\hline\n")
            fragment:write("\\textbf{Property} & \\textbf{Result (var-elim)} & \\multicolumn{2}{c}{\\textbf{Time (s)}} \\\\\n")
            fragment:write("\\cline{3-4}\n")
            fragment:write(" & & \\textbf{var-elim} & \\textbf{sampling} \\\\\n")
            fragment:write("\\hline\n")
            
            for _, name in ipairs(exp_names) do
                local exp = experiments_by_name[name]
                local res = results_by_name[name]
                local abbr = get_abbreviation(name)
                
                local prop_name = use_abbreviated and "\\prop{" .. escape_bprint(abbr) .. "}" or "\\bprint{" .. bprint_breakable(exp.property) .. "}"
                local var_elim_result = res and format_result(res.var_elim_result) or "N/A"
                local var_elim_time = res and format_time_or_failure(res.var_elim_result, res.var_elim_time) or "N/A"
                local sampling_time = res and format_time_or_failure(res.sampling_result, res.sampling_time) or "N/A"
                
                -- \bprint adds its own break opportunities between tokens
                local result_format = "\\bprint{" .. bprint_breakable(var_elim_result) .. "}"

                
                fragment:write(string.format("%s & %s & %s & %s \\\\\n",
                    prop_name, result_format, var_elim_time, sampling_time))
            end
            
            fragment:write("\\hline\n")
            fragment:write("\\end{tabularx}\n")
            fragment:write("\\endgroup\\par\n")
            fragment:close()
        end

    else
        fragment = io.open(fragment_filename, 'w')
        if not fragment then
            print("ERROR: Could not open " .. fragment_filename)
            return
        end
        
        -- Group experiments by model for proper ordering
        local model_groups = {}
        for name, exp in pairs(experiments_by_name) do
            if experiment_set[name] then
                local model = exp.model
                if not model_groups[model] then
                    model_groups[model] = {}
                end
                table.insert(model_groups[model], name)
            end
        end
        
        -- Sort models by variable count
        local sorted_models = {}
        for model in pairs(model_groups) do
            table.insert(sorted_models, model)
        end
        table.sort(sorted_models, function(a, b)
            return MODEL_VAR_COUNTS[a] < MODEL_VAR_COUNTS[b]
        end)
        
        -- Generate content for each model
        for _, model in ipairs(sorted_models) do
            local exp_names = model_groups[model]
            
            fragment:write("\\noindent\n")
            fragment:write("\\textbf{\\large " .. escape_latex(model) .. " (" .. MODEL_VAR_COUNTS[model] .. " variables)}\n")
            fragment:write("\\input{" .. escape_latex(model) .. ".tex}\n")
            
            -- Add property descriptions for this model
            local prefix = use_full_prefix and "property_descriptions_full_" or "property_descriptions_"
            fragment:write("\\input{" .. prefix .. escape_latex(model) .. ".tex}\n")
            fragment:write("\\vspace{0.2cm}\n")
            
            fragment:write("\\begin{longtable}{p{3cm} p{6cm} c c}\n")
            fragment:write("\\toprule\n")
            fragment:write("\\textbf{Property} & \\textbf{Result (var\\_elim)} & \\multicolumn{2}{c}{\\textbf{Avg. Time (s)}}\n")
            fragment:write("\\\\\n")
            fragment:write("\\cmidrule(lr){3-4}\n")
            fragment:write(" & & \\textbf{var\\_elim} & \\textbf{sampling}\n")
            fragment:write("\\\\\n")
            fragment:write("\\midrule\n")
            fragment:write("\\endhead\n")
            fragment:write("\\midrule\n")
            fragment:write("\\endfoot\n")
            fragment:write("\\bottomrule\n")
            fragment:write("\\endlastfoot\n")
            
            -- Use order_list if provided, otherwise use exp_names as-is
            local ordered_names = order_list or exp_names
            for _, name in ipairs(ordered_names) do
                if experiment_set[name] and experiments_by_name[name] and experiments_by_name[name].model == model then
                    local exp = experiments_by_name[name]
                    local res = results_by_name[name]
                    local expl = explanations_by_name[name]
                    local abbr = get_abbreviation(name)
                    
                    local prop_name = use_abbreviated and "\\prop{" .. escape_bprint(abbr) .. "}" or "\\bprint{" .. bprint_breakable(exp.property) .. "}"
                    local var_elim_result = res and format_result(res.var_elim_result) or "N/A"
                    local var_elim_time = res and format_time_or_failure(res.var_elim_result, res.var_elim_time) or "N/A"
                    local sampling_time = res and format_time_or_failure(res.sampling_result, res.sampling_time) or "N/A"
                    
                    local result_format = "\\bprint{" .. bprint_breakable(var_elim_result) .. "}"

                    
                    fragment:write(string.format("%s & %s & %s & %s \\\\\n",
                        prop_name, result_format, var_elim_time, sampling_time))
                    
                    -- Add description if available
                    if expl and expl.explanation then
                        local question = exp.description or ""
                        local answer = expl.explanation or ""
                        fragment:write(string.format("\\multicolumn{4}{p{12cm}}{\\footnotesize %s. %s \\vspace{4pt}} \\\\\n",
                            escape_latex(question), escape_latex(answer)))
                    end
                end
            end
            
            fragment:write("\\end{longtable}\n")
            fragment:write("\\vspace{-0.2cm}\n")
        end
        
        fragment:close()
    end
end

-- Generate model overview table
local function generate_model_table()
    local model_table = io.open("overleaf/experiments/model_table.tex", 'w')
    
    model_table:write("\\begin{table}[t]\n")
    model_table:write("\\centering\n")
    model_table:write("\\caption{Bayesian networks used in experiments.\nMax: maximum average solving time over 10 runs, successful runs only.}\n")
    model_table:write("\\label{tab:models}\n")
    model_table:write("\\small\n")
    model_table:write("\\begin{tabularx}{\\textwidth}{@{}lYrrr@{}}\n")
    model_table:write("\\toprule\n")
    model_table:write("\\textbf{Model} & \\textbf{Domain} & \\textbf{\\#Vars} & \\textbf{\\#Props} & \\textbf{Max (s)} \\\\\n")
    model_table:write("\\midrule\n")
    
    -- Count properties per model
    local model_prop_counts = {}
    for name, exp in pairs(experiments_by_name) do
        local model = exp.model
        if not model_prop_counts[model] then
            model_prop_counts[model] = 0
        end
        model_prop_counts[model] = model_prop_counts[model] + 1
    end
    
    -- Calculate min and max times per model (only for successful runs)
    local model_times = {}
    for name, exp in pairs(experiments_by_name) do
        local model = exp.model
        local res = results_by_name[name]
        if res then
            local function is_successful(result)
                if not result then return false end
                if result == "Crash" then return false end
                if result:find("ERROR:") then return false end
                if result:find("Mem out") then return false end
                return true
            end
            
            if not model_times[model] then
                model_times[model] = {}
            end
            
            if is_successful(res.var_elim_result) and res.var_elim_time and tonumber(res.var_elim_time) and tonumber(res.var_elim_time) > 0 then
                table.insert(model_times[model], tonumber(res.var_elim_time))
            end
            if is_successful(res.sampling_result) and res.sampling_time and tonumber(res.sampling_time) and tonumber(res.sampling_time) > 0 then
                table.insert(model_times[model], tonumber(res.sampling_time))
            end
        end
    end
    
    -- Write rows for each model
    local sorted_models = {}
    for model in pairs(MODEL_VAR_COUNTS) do
        table.insert(sorted_models, model)
    end
    table.sort(sorted_models, function(a, b)
        return MODEL_VAR_COUNTS[a] < MODEL_VAR_COUNTS[b]
    end)
    
    for _, model in ipairs(sorted_models) do
        local model_escaped = escape_latex(model)
        local domain = MODEL_DOMAINS[model] or ""
        local prop_count = model_prop_counts[model] or 0
        local var_count = MODEL_VAR_COUNTS[model] or 0
        
        -- Calculate max time for this model
        local max_time
        local times = model_times[model] or {}
        if #times > 0 then
            table.sort(times)
            max_time = format_time(times[#times])
        else
            max_time = "N/A"
        end
        
        model_table:write(string.format("%s & %s & %d & %d & %s \\\\\n",
            model_escaped, escape_latex(domain), var_count, prop_count, escape_latex(max_time)))
    end
    
    model_table:write("\\bottomrule\n")
    model_table:write("\\end{tabularx}\n")
    model_table:write("\\end{table}\n")
    model_table:close()
    
    print("Model table saved to overleaf/experiments/model_table.tex")
end

-- Main execution
local mode = (arg and arg[1]) or "all"

if mode ~= "model-only" and mode ~= "descriptions-only" then
    print("Generating tables for chosen experiments...")
    generate_latex_tables(
        chosen_experiments,
        "overleaf/experiments/summary_table_fragment.tex",
        "overleaf/experiments/summary_table.tex",
        true,   -- use abbreviated names
        false,  -- do not include descriptions
        true,   -- separate files per model
        chosen_order  -- preserve order from chosen.csv
    )
    print("LaTeX fragment saved to overleaf/experiments/summary_table_fragment.tex")
end

if mode == "descriptions-only" or mode == "all" then
    generate_itemize_descriptions(
        chosen_experiments,
        "overleaf/experiments/property_descriptions.tex",
        true,   -- separate files per model
        false  -- no full prefix for main part
    )
    print("Property descriptions saved to overleaf/experiments/property_descriptions_*.tex")
end

if mode ~= "model-only" and mode ~= "descriptions-only" then
    -- Generate full tables for all experiments
    print("Preparing to generate full table for all experiments...")
    local all_experiments = {}
    for name in pairs(experiments_by_name) do
        all_experiments[name] = true
    end
    print("Found " .. count_table(all_experiments) .. " total experiments")

    generate_latex_tables(
        all_experiments,
        "overleaf/experiments/summary_table_fragment_full.tex",
        "overleaf/experiments/summary_table_full.tex",
        true,   -- use abbreviated property names
        false,  -- do not include descriptions
        true    -- separate files per model
    )
    print("LaTeX fragment (full) saved to overleaf/experiments/summary_table_fragment_full.tex")
end

if mode == "descriptions-only" or mode == "all" then
    -- Generate full property descriptions for appendix
    print("Preparing to generate full property descriptions for all experiments...")
    local all_experiments = {}
    for name in pairs(experiments_by_name) do
        all_experiments[name] = true
    end
    generate_itemize_descriptions(
        all_experiments,
        "overleaf/experiments/property_descriptions_full.tex",
        true,   -- separate files per model
        true    -- full prefix for appendix
    )
    print("Property descriptions (full) saved to overleaf/experiments/property_descriptions_full.tex")
end

-- Generate model table (skip if only regenerating descriptions)
if mode ~= "descriptions-only" then
    generate_model_table()
end

-- Copy all generated files to Overleaf directory
print("Copying files to Overleaf directory...")
print("Files copied to Overleaf directory")

print("Done!")
