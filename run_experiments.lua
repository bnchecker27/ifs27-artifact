#!/usr/bin/env luajit
-- Script to run experiments from experiments.csv and output results to results.csv

local io = io
local os = os
local string = string
local table = table
local math = math
local ffi = require("ffi")

-- Fixed seed for reproducibility
local SEED = 42

-- FFI bindings for high-resolution timing
ffi.cdef[[
struct timeval {
    long tv_sec;
    long tv_usec;
};
int gettimeofday(struct timeval *tv, void *tz);
]]

local function get_time()
    local tv = ffi.new("struct timeval")
    ffi.C.gettimeofday(tv, nil)
    return tonumber(tv.tv_sec) + tonumber(tv.tv_usec) / 1000000
end

math.randomseed(SEED)

-- Configuration
local EXPERIMENTS_CSV = "overleaf/experiments/experiments.csv"
local RESULTS_CSV = "overleaf/experiments/results.csv"
local MODELS_DIR = "models"
local DOCKER_IMAGE = "bayesian-luajit"
local MAIN_LUA = "main.lua"
local NUM_SAMPLES = "1E7"
local NUM_REPETITIONS = 10

-- Parse command-line options
for i = 1, #arg do
    if arg[i] == "--single-run" then
        NUM_REPETITIONS = 1
        print("Single-run mode enabled: each experiment will be run once.")
        io.flush()
        break
    end
end

-- Always run luajit directly inside artifact (Docker-in-Docker doesn't work)
local USE_DOCKER = false
local LUAJIT_BIN = os.getenv("LUAJIT")
if not LUAJIT_BIN then
    -- prefer a luajit on PATH; the packaged Docker image's install
    -- prefix is the fallback (this script also runs inside the image)
    local pipe = io.popen("command -v luajit 2>/dev/null")
    local found = pipe and pipe:read("*l") or nil
    if pipe then pipe:close() end
    LUAJIT_BIN = (found and found ~= "") and found or "/usr/local/bin/luajit"
end

-- Per-engine solver for each query head.  IDP/INFL have a single
-- solver (no sampling variant) — both columns genuinely coincide for
-- formulas using only those heads.
local HEAD_SOLVERS = {
    ["P("]    = {"prob_var_elim", "prob_sample"},
    ["MAP("]  = {"map_var_elim",  "map_sample"},
    ["MPE("]  = {"mpe_var_elim",  "mpe_sample"},
    ["IDP("]  = {"idp",           "idp"},
    ["INFL("] = {"infl",          "infl"},
}
local HEAD_ORDER = {"P(", "MAP(", "MPE(", "IDP(", "INFL("}

-- All head occurrences, not just the first token: a composite like
-- "P(x)>=0.5∧INFL(y,z)" needs both families, and a formula starting
-- with "0.5-…", "INFL(…" or "!IDP(…" has no leading P(/MAP(/MPE( —
-- the old first-token check silently fell back to prob_var_elim for
-- the "sampling" column too.  The %f[%w_] frontier keeps "P(" from
-- matching inside "MAP(".
local function heads_in(property_str)
    local found = {}
    for _, head in ipairs(HEAD_ORDER) do
        local pat = "%f[%w_]" .. head:sub(1, -2) .. "%("
        if property_str:find(pat) then
            found[head] = true
        end
    end
    return found
end

-- -> enable-list for the var_elim run, enable-list for the sampling
-- run, disable-list for the sampling run (the var_elim counterparts of
-- every sampling-sensitive head — disabling them lets the sampler take
-- the query; engine-neutral heads need no disable)
local function solvers_for_property(property_str)
    local heads = heads_in(property_str)
    local var_elim, sample, disable = {}, {}, {}
    for _, head in ipairs(HEAD_ORDER) do
        if heads[head] then
            local pair = HEAD_SOLVERS[head]
            var_elim[#var_elim + 1] = pair[1]
            sample[#sample + 1] = pair[2]
            if pair[1] ~= pair[2] then
                disable[#disable + 1] = pair[1]
            end
        end
    end
    if #var_elim == 0 then
        -- no query head (a bare variable / pure claim): keep the
        -- historical fallback so the columns behave as before
        var_elim = {"prob_var_elim"}
        sample = {"prob_sample"}
        disable = {"prob_var_elim"}
    end
    return table.concat(var_elim, ","), table.concat(sample, ","),
           table.concat(disable, ",")
end

-- CSV parsing function
local function parse_csv_line(line, delimiter)
    local result = {}
    local field = ""
    local in_quotes = false
    local i = 1
    
    while i <= #line do
        local char = line:sub(i, i)
        
        if char == '"' then
            in_quotes = not in_quotes
        elseif char == delimiter and not in_quotes then
            table.insert(result, field)
            field = ""
        else
            field = field .. char
        end
        i = i + 1
    end
    
    table.insert(result, field)
    return result
end

-- Read CSV file and return headers and rows
local function read_csv(filename, delimiter)
    delimiter = delimiter or ','
    local file = io.open(filename, 'r')
    if not file then
        return nil, nil
    end
    
    local headers = parse_csv_line(file:read('*l'), delimiter)
    -- Strip whitespace/newlines from headers
    for i, h in ipairs(headers) do
        headers[i] = h:gsub('%s+$', '')  -- strip trailing whitespace
    end
    local rows = {}
    
    for line in file:lines() do
        if line:match('%S') then
            local values = parse_csv_line(line, delimiter)
            local row = {}
            for i, header in ipairs(headers) do
                row[header] = values[i] or ''
            end
            table.insert(rows, row)
        end
    end
    
    file:close()
    return headers, rows
end

-- Write CSV file
local function write_csv(filename, headers, rows)
    local file = io.open(filename, 'w')
    if not file then
        return false
    end
    
    file:write(table.concat(headers, ',') .. '\n')
    for _, row in ipairs(rows) do
        local values = {}
        for _, header in ipairs(headers) do
            local value = row[header] or ''
            -- Escape quotes and wrap in quotes if contains comma or quote
            if value:find('[",]') then
                value = '"' .. value:gsub('"', '""') .. '"'
            end
            table.insert(values, value)
        end
        file:write(table.concat(values, ',') .. '\n')
    end
    
    file:close()
    return true
end



-- Run a single experiment
local function run_experiment(model_path, property_str, solver, num_samples, disable_solver)
    local cmd
    
    if USE_DOCKER then
        -- Get current working directory
        local pwd = io.popen("pwd"):read("*a"):gsub("%s+$", "")
        cmd = {
            "docker", "run", "--rm",
            "--entrypoint", "/usr/local/bin/luajit",
            "-v", pwd .. ":/app",
            DOCKER_IMAGE,
            MAIN_LUA,
            "--model", model_path,
            "--property", property_str,
            "--enable_solvers", solver
        }
    else
        cmd = {
            LUAJIT_BIN,
            MAIN_LUA,
            "--model", model_path,
            "--property", property_str,
            "--enable_solvers", solver
        }
    end
    
    if num_samples then
        table.insert(cmd, "--num_samples")
        table.insert(cmd, num_samples)
    end

    -- Numeric outcome literals (e.g. pigs' =0/=1/=2) need the numval
    -- feature under the current parser
    if property_str:find("=%d") then
        table.insert(cmd, "--features")
        table.insert(cmd, "numval")
    end
    
    table.insert(cmd, "--seed")
    table.insert(cmd, tostring(SEED))
    
    if disable_solver then
        table.insert(cmd, "--disable_solvers")
        table.insert(cmd, disable_solver)
    end
    
    -- Build command string with proper escaping
    local cmd_str = ""
    for i, arg in ipairs(cmd) do
        -- Quote arguments that contain special shell characters
        if arg:find('[()|&<>; \t\n]') then
            arg = "'" .. arg:gsub("'", "'\\''") .. "'"
        end
        cmd_str = cmd_str .. (i > 1 and " " or "") .. arg
    end
    
    -- Execute command with timeout
    local start_time = get_time()
    local output_file = os.tmpname()
    local error_file = os.tmpname()
    
    -- Run command
    local full_cmd = cmd_str .. " >" .. output_file .. " 2>" .. error_file
    local result = os.execute(full_cmd)
    local end_time = get_time()
    local runtime = end_time - start_time
    
    -- Read output
    local out_f = io.open(output_file, 'r')
    local err_f = io.open(error_file, 'r')
    
    local stdout = out_f and out_f:read('*a') or ""
    local stderr = err_f and err_f:read('*a') or ""
    
    if out_f then out_f:close() end
    if err_f then err_f:close() end
    
    os.remove(output_file)
    os.remove(error_file)
    
    -- Check for errors
    -- os.execute returns true on success, not 0
    if not result then
        return nil, runtime, stderr:gsub("%s+$", "")
    end
    
    -- Parse output
    stdout = stdout:gsub("%s+$", "")
    
    if stdout:find("Result: ") then
        local result_str = stdout:match("Result: (.*)")
        result_str = result_str:gsub("\n", " "):gsub("\r", ""):gsub("^%s+", ""):gsub("%s+$", "")
        return result_str, runtime, nil
    elseif stdout:find("Probability: ") then
        local result_str = stdout:match("Probability: (.*)")
        return result_str, runtime, nil
    else
        local sanitized = stdout:gsub("\n", " "):gsub("\r", ""):gsub("^%s+", ""):gsub("%s+$", "")
        return sanitized, runtime, nil
    end
end

-- Main function
local function main()
    -- Read experiments
    local _, experiments_rows = read_csv(EXPERIMENTS_CSV, ';')
    print("Found " .. #experiments_rows .. " experiments in experiments.csv.")
    
    -- Load existing results
    local existing_results = {}
    local results_file = io.open(RESULTS_CSV, 'r')
    if results_file then
        results_file:close()
        local _, results_rows = read_csv(RESULTS_CSV)
        for _, row in ipairs(results_rows) do
            local key = row.name .. "|" .. row.engine
            existing_results[key] = row
        end
        local count = 0
        for _ in pairs(existing_results) do count = count + 1 end
        print("Loaded " .. count .. " existing results from " .. RESULTS_CSV .. ".")
    else
        print("No existing results file found at " .. RESULTS_CSV .. ".")
    end
    
    -- Prepare results (start with existing)
    local results = {}
    for _, row in pairs(existing_results) do
        table.insert(results, row)
    end
    
    -- Count new experiments to run
    local new_experiments = {}
    for _, exp in ipairs(experiments_rows) do
        local name = exp.name
        if not existing_results[name .. "|var_elim"] or not existing_results[name .. "|sampling"] then
            table.insert(new_experiments, exp)
        end
    end
    
    print("Running " .. #new_experiments .. " new experiments (skipping " .. (#experiments_rows - #new_experiments) .. " with existing results).")
    
    for i, exp in ipairs(new_experiments) do
        local name = exp.name
        local model = exp.model
        local property_str = exp.property
        
        local model_path
        if USE_DOCKER then
            model_path = "/app/" .. MODELS_DIR .. "/" .. model .. ".bif"
        else
            model_path = MODELS_DIR .. "/" .. model .. ".bif"
        end
        
        print("\n[" .. i .. "/" .. #new_experiments .. "] Running: " .. name)
        print("  Model: " .. model)
        print("  Property: " .. property_str)
        io.flush()
        
        -- Check if model file exists
        local local_model_path = MODELS_DIR .. "/" .. model .. ".bif"
        local model_file = io.open(local_model_path, 'r')
        if not model_file then
            print("  ERROR: Model file not found: " .. local_model_path)
            table.insert(results, {
                name = name,
                engine = 'var_elim',
                result = 'ERROR: Model file not found',
                runtime = '0'
            })
            table.insert(results, {
                name = name,
                engine = 'sampling',
                result = 'ERROR: Model file not found',
                runtime = '0'
            })
        else
            model_file:close()
            
            -- Run with variable elimination
            local var_elim_solver, sample_solver_new, sample_disable
                = solvers_for_property(property_str)
            
            print("  Running with variable elimination (" .. var_elim_solver .. ", " .. NUM_REPETITIONS .. " repetitions)...")
            io.flush()
            
            local var_result, var_total_runtime, var_error = nil, 0, nil
            for _ = 1, NUM_REPETITIONS do
                local res, rt, err = run_experiment(model_path, property_str, var_elim_solver)
                if err then
                    var_error = err
                    break
                end
                var_result = res
                var_total_runtime = var_total_runtime + rt
            end
            
            local var_result_str
            if var_error then
                print("    ERROR: " .. var_error)
                var_result_str = "ERROR: " .. var_error
            else
                local var_avg_runtime = var_total_runtime / NUM_REPETITIONS
                print("    Result: " .. var_result)
                print("    Avg. runtime: " .. string.format("%.2f", var_avg_runtime) .. "s")
                var_result_str = tostring(var_result)
            end
            io.flush()
            
            table.insert(results, {
                name = name,
                engine = 'var_elim',
                result = var_result_str,
                runtime = var_error and "0" or string.format("%.2f", var_total_runtime / NUM_REPETITIONS)
            })
            
            -- Run with sampling
            local sample_solver = sample_solver_new
            
            print("  Running with sampling (" .. sample_solver .. ", " .. NUM_SAMPLES .. " samples, " .. NUM_REPETITIONS .. " repetitions)...")
            io.flush()
            
            local disable_solver
            if sample_disable ~= "" then
                disable_solver = sample_disable
            end
            
            local sample_result, sample_total_runtime, sample_error = nil, 0, nil
            for _ = 1, NUM_REPETITIONS do
                local res, rt, err = run_experiment(model_path, property_str, sample_solver, NUM_SAMPLES, disable_solver)
                if err then
                    sample_error = err
                    break
                end
                sample_result = res
                sample_total_runtime = sample_total_runtime + rt
            end
            
            local sample_result_str
            if sample_error then
                print("    ERROR: " .. sample_error)
                sample_result_str = "ERROR: " .. sample_error
            else
                local sample_avg_runtime = sample_total_runtime / NUM_REPETITIONS
                print("    Result: " .. sample_result)
                print("    Avg. runtime: " .. string.format("%.2f", sample_avg_runtime) .. "s")
                sample_result_str = tostring(sample_result)
            end
            io.flush()
            
            table.insert(results, {
                name = name,
                engine = 'sampling',
                result = sample_result_str,
                runtime = sample_error and "0" or string.format("%.2f", sample_total_runtime / NUM_REPETITIONS)
            })
        end
    end
    
    -- Write results
    print("\nWriting results to " .. RESULTS_CSV .. "...")
    io.flush()
    
    local headers = {'name', 'engine', 'result', 'runtime'}
    write_csv(RESULTS_CSV, headers, results)
    
    print("Done! Results written to " .. RESULTS_CSV)
    print("Total experiments in config: " .. #experiments_rows)
    print("Total result entries: " .. #results)
    print("New experiments run: " .. #new_experiments)
end

main()
