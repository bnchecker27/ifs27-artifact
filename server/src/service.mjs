// Service layer for the RPM protocol.  Transport-agnostic: used by the
// TCP server, the WebSocket server, and the in-page web worker.
//
// ALL logic lives in Lua — lua/service.lua + lua/validate.lua +
// nuklear-ime-demo/json.lua — loaded into the WASM Lua runtime below.
// The same sources run under LuaJIT in the native server (server.lua),
// so Node is only a host: Lua runtime + file persistence + transports.
//
// createService(env) -> { createSession(write), lua }
//
//   createSession(write): per-connection state.  write(json) sends a
//   JSON string back to the client.
//   lua: the Lua runtime handle (for direct eval in tests/tooling).

import { newLua } from '../../public/lua-interop.js';

// In Node this file lives at server/src/service.mjs; in the browser it
// is imported by /public/server-worker.mjs — either way these URLs
// resolve relative to this module:
const jsURL   = new URL('../../public/lua-5.4.7-with-ffi.js',   import.meta.url).href;
const wasmURL = new URL('../../public/lua-5.4.7-with-ffi.wasm', import.meta.url).href;

const MODEL_FILE =
    (typeof process !== 'undefined' && process.env?.BAYESL_MODEL_FILE)
        ? process.env.BAYESL_MODEL_FILE
        : new URL('../model.json', import.meta.url).pathname;

// filesystem persistence is only available on the Node side
let fs = null;
// Only try to load Node's fs module when actually running in Node; the
// dynamic import would otherwise trigger a CORS error in the browser worker.
if (typeof process !== 'undefined' && process.versions?.node) {
    try {
        fs = await import('node:fs');
    } catch (_) { /* keep the model in memory */ }
}

// Read a Lua source file.  In Node the URL is file://; in the worker it
// is fetched over HTTP.
async function loadText(url) {
    if (fs && url.startsWith('file:')) {
        return fs.readFileSync(new URL(url), 'utf8');
    }
    const r = await fetch(url, { cache: 'no-store' });
    if (!r.ok) throw new Error('cannot load ' + url + ': HTTP ' + r.status);
    return r.text();
}

// Parser/explainer/tree modules needed for formula editing and the
// formula-tree view.  These are fetched the first time a formula-related
// request arrives so the worker starts quickly.
const FORMULA_MODULES = [
    { name: 'lib.util',                path: '../../lib/util.lua' },
    { name: 'lib.lpeg_util',           path: '../../lib/lpeg_util.lua' },
    { name: 'lib.positional',          path: '../../lib/positional.lua' },
    { name: 'lib.parsing_context',     path: '../../lib/parsing_context.lua' },
    { name: 'lib.features',            path: '../../lib/features.lua' },
    { name: 'logic.operators',         path: '../../logic/operators.lua' },
    { name: 'logic.logic',             path: '../../logic/logic.lua' },
    { name: 'logic.explainer',         path: '../../logic/explainer.lua' },
    { name: 'logic.parser_formula',    path: '../../logic/parser_formula.lua' },
    { name: 'logic.parser_identifier', path: '../../logic/parser_identifier.lua' },
    { name: 'logic.parser_box',        path: '../../logic/parser_box.lua' },
    { name: 'logic.constant',          path: '../../logic/constant.lua' },
    { name: 'logic.parser_real',       path: '../../logic/parser_real.lua' },
    { name: 'logic.parser_infl',       path: '../../logic/parser_infl.lua' },
    { name: 'logic.parser_idp',        path: '../../logic/parser_idp.lua' },
    { name: 'logic.parser_map',        path: '../../logic/parser_map.lua' },
    { name: 'logic.parser_mpe',        path: '../../logic/parser_mpe.lua' },
    { name: 'logic.parser_prob_quantifier', path: '../../logic/parser_prob_quantifier.lua' },
    { name: 'logic.parser_modify_probability', path: '../../logic/parser_modify_probability.lua' },
    { name: 'logic.dist_family',       path: '../../logic/dist_family.lua' },
    { name: 'logic.suggestions',       path: '../../logic/suggestions.lua' },
    // varterm requires compute_shared_order (a pure ordering helper) at
    // module level — it must live in THIS set even though it sits in
    // model_checker/, or any check_formula touching a varterm node
    // before the first evaluate dies on the missing preload.
    { name: 'model_checker.compute_shared_order',  path: '../../model_checker/compute_shared_order.lua' },
    { name: 'logic.varterm',           path: '../../logic/varterm.lua' },
    { name: 'logic.parser_bn_logic',   path: '../../logic/parser_bn_logic.lua' },
    { name: 'logic.tree_layout',       path: '../../logic/tree_layout.lua' },
    { name: 'logic.tree_graphviz',     path: '../../logic/tree_graphviz.lua' },
];

// Bayesian-network builder loaded when a model is present; needed for
// semantic validation in check_formula and for model checking.
const BN_MODULES = [
    { name: 'bayesian_network.bayesian_network', path: '../../bayesian_network/bayesian_network.lua' },
    { name: 'bayesian_network.bn_to_bif',        path: '../../bayesian_network/bn_to_bif.lua' },
    { name: 'bayesian_network.bn_to_model',      path: '../../bayesian_network/bn_to_model.lua' },
    { name: 'bayesian_network.bn_to_tuple',      path: '../../bayesian_network/bn_to_tuple.lua' },
    { name: 'bayesian_network.parser_bif',       path: '../../bayesian_network/parser_bif.lua' },
];

// Model checker and supporting modules loaded on the first evaluate request.
const MODEL_CHECKER_MODULES = [
    { name: 'lib.program_options',     path: '../../lib/program_options.lua' },
    { name: 'lib.options_manager',     path: '../../lib/options_manager.lua' },
    { name: 'model_checker.compute_graphs',        path: '../../model_checker/compute_graphs.lua' },
    { name: 'model_checker.bindings',              path: '../../model_checker/bindings.lua' },
    { name: 'model_checker.boolean_claim',         path: '../../model_checker/boolean_claim.lua' },
    { name: 'model_checker.dependence',            path: '../../model_checker/dependence.lua' },
    { name: 'model_checker.evidencer',             path: '../../model_checker/evidencer.lua' },
    { name: 'model_checker.find_reachable',        path: '../../model_checker/find_reachable.lua' },
    { name: 'model_checker.model_checker',         path: '../../model_checker/model_checker.lua' },
    { name: 'model_checker.mutable_bn',            path: '../../model_checker/mutable_bn.lua' },
    { name: 'model_checker.operators_binary_semantics',  path: '../../model_checker/operators_binary_semantics.lua' },
    { name: 'model_checker.operators_compare_semantics', path: '../../model_checker/operators_compare_semantics.lua' },
    { name: 'model_checker.result_display',        path: '../../model_checker/result_display.lua' },
    { name: 'model_checker.sampler_auto',          path: '../../model_checker/sampler_auto.lua' },
    { name: 'model_checker.sampler_enumerate',     path: '../../model_checker/sampler_enumerate.lua' },
    { name: 'model_checker.sampler_random',        path: '../../model_checker/sampler_random.lua' },
    { name: 'model_checker.solver_arithmetic_operator',  path: '../../model_checker/solver_arithmetic_operator.lua' },
    { name: 'model_checker.solver_boolean_operator',     path: '../../model_checker/solver_boolean_operator.lua' },
    { name: 'model_checker.solver_idp',            path: '../../model_checker/solver_idp.lua' },
    { name: 'model_checker.solver_infl',           path: '../../model_checker/solver_infl.lua' },
    { name: 'model_checker.solver_map_sample',     path: '../../model_checker/solver_map_sample.lua' },
    { name: 'model_checker.solver_map_var_elim',   path: '../../model_checker/solver_map_var_elim.lua' },
    { name: 'model_checker.solver_modify_probability', path: '../../model_checker/solver_modify_probability.lua' },
    { name: 'model_checker.solver_mpe_sample',     path: '../../model_checker/solver_mpe_sample.lua' },
    { name: 'model_checker.solver_mpe_var_elim',   path: '../../model_checker/solver_mpe_var_elim.lua' },
    { name: 'model_checker.solver_numeric_compare',   path: '../../model_checker/solver_numeric_compare.lua' },
    { name: 'model_checker.solver_prob_sample',    path: '../../model_checker/solver_prob_sample.lua' },
    { name: 'model_checker.solver_prob_var_elim',  path: '../../model_checker/solver_prob_var_elim.lua' },
    { name: 'model_checker.solver_value',          path: '../../model_checker/solver_value.lua' },
    { name: 'model_checker.solver_value_compare',  path: '../../model_checker/solver_value_compare.lua' },
    { name: 'model_checker.solver_variable',       path: '../../model_checker/solver_variable.lua' },
    { name: 'model_checker.solver_variable_compare', path: '../../model_checker/solver_variable_compare.lua' },
    { name: 'model_checker.static_bn',             path: '../../model_checker/static_bn.lua' },
    { name: 'model_checker.toposort',              path: '../../model_checker/toposort.lua' },
];

export async function createService(env) {
    const lua = await newLua({
        luaJSPath: jsURL,
        locateFile: () => wasmURL,
        print:    s => console.log('[lua]', s),
        printErr: s => console.error('[lua]', s),
    });
    // newLua only loads the runtime — the Lua state is created
    // explicitly (lua.run would otherwise run against a null state)
    globalThis.window ??= globalThis;   // luaopen_js touches `window`
    await lua.newState();

    // Optional web Graphviz layout: the Lua side checks js.global.graphviz_layout
    // and, if present, calls it with the DOT source, returning plain text.
    try {
        // propagate the deploy version (?v=) passed to this module so the
        // graphviz import is cache-busted too
        const v = new URL(import.meta.url).searchParams.get('v');
        const vizUrl = new URL(
            '../../public/node_modules/@viz-js/viz/dist/viz.js',
            import.meta.url);
        if (v) vizUrl.searchParams.set('v', v);
        const { instance } = await import(vizUrl.href);
        if (typeof instance === 'function') {
            const viz = await instance();
            // lua-interop.js's __call wrapper passes the first Lua argument
            // as `this`, so the function reads from `this` rather than using a
            // parameter.  It also accepts a normal first argument when called
            // from JavaScript.
            globalThis.graphviz_layout = function () {
                // lua-interop.js's __call wrapper puts the first Lua
                // argument on `this`; a second Lua argument (the engine)
                // arrives as arguments[0].  Plain JS calls pass both
                // positionally.
                const dot = (typeof this === 'string') ? this : arguments[0];
                const engine = (typeof this === 'string')
                    ? arguments[0] : arguments[1];
                if (typeof dot !== 'string') return null;
                try {
                    return viz.renderString(dot,
                        { format: 'plain',
                          engine: (typeof engine === 'string' && engine)
                                  || 'dot' });
                } catch (e) {
                    console.error('[graphviz]', e);
                    return null;
                }
            };
        }
    } catch (e) {
        console.log('[graphviz] not available:', e.message);
    }

    // The deploy's cache-bust (?v= on this module's URL) must reach
    // every Lua source fetch — without it the browser can mix a stale
    // cached service.lua/varterm.lua with fresh fetched modules and
    // the whole worker session errors out on requires.
    const deployV = new URL(import.meta.url).searchParams.get('v');
    const srcURL = (p) => {
        const u = new URL(p, import.meta.url);
        if (deployV) u.searchParams.set('v', deployV);
        return u.href;
    };

    // service.lua receives its dependencies as source strings and
    // returns the dispatch function: raw JSON in, raw JSON out.
    // The web worker has no filesystem, so the parser modules are
    // also passed as source and registered via package.preload.
    const [jsonSrc, validateSrc, serviceSrc, examplesSrc, examplesW95Src] = await Promise.all([
        loadText(srcURL('../../nuklear-ime-demo/json.lua')),
        loadText(srcURL('../lua/validate.lua')),
        loadText(srcURL('../lua/service.lua')),
        loadText(srcURL('../lua/examples.lua')),
        loadText(srcURL('../lua/examples_win95.lua')),
    ]);
    const sources = { "server.lua.examples": examplesSrc,
                      "server.lua.examples_win95": examplesW95Src };
    const bnDispatch = (await lua.run(serviceSrc, jsonSrc, validateSrc, sources))[0];

    // Web worker modules are loaded on demand: the worker has no filesystem,
    // and preloading all of them on startup makes the browser smoke test
    // time out against the single-threaded dev server.  Native runs use
    // package.path and never trigger this path.
    function makeLoader(modules) {
        // Memoize the in-flight promise, not just the result: the page's
        // startup burst (get_model/set_model/check_formula/…) dispatches
        // several requests before the first fetch resolves, and without
        // a shared promise each would refetch the whole module set — on
        // a remote host that multiplied ~30 files into ~90 serial-ish
        // requests and pushed the first evaluate past half a minute.
        // On failure the promise is cleared so the next request retries
        // the whole set (a partially filled set would register
        // permanently incomplete package.preload entries).
        let inflight = null;
        return function ensureSources() {
            if (!inflight) {
                inflight = loadAll();
                inflight.catch(() => { inflight = null; });
            }
            return inflight;
        };
        async function loadAll() {
            const fetched = {};
            await Promise.all(modules.map(async (m) => {
                fetched[m.name] = await loadText(srcURL(m.path));
            }));
            lua.run(`
                local sources = ...
                if type(sources) == "table" then
                    for name, src in pairs(sources) do
                        package.preload[name] = function()
                            local chunk, err = load(src, name)
                            if not chunk then error(err) end
                            return chunk()
                        end
                    end
                end
            `, fetched);
        }
    }
    const ensureFormulaSources = makeLoader(FORMULA_MODULES);
    const ensureBnSources = makeLoader(BN_MODULES);
    const ensureModelCheckerSources = makeLoader(MODEL_CHECKER_MODULES);

    // restore the stored model once, if the host has a filesystem
    if (fs) {
        try {
            const stored = JSON.parse(fs.readFileSync(MODEL_FILE, 'utf8'));
            await bnDispatch(JSON.stringify(
                {method: 'restore_model', model: stored}));
            console.log('model restored from', MODEL_FILE);
        } catch (_) { /* no stored model yet */ }
    }

    async function dispatch(msg) {
        // msg_features requires lib.features (FORMULA_MODULES) — every
        // method that parses a `features` field needs the sources,
        // not just the formula ones: a set_model/load_example_model
        // arriving before the first check_formula would otherwise hit
        // the unregistered package.preload and fail in the fs-less
        // worker (locally invisible — the fetch wins the race anyway)
        if (msg.method === 'check_formula' || msg.method === 'evaluate'
            || msg.method === 'get_tree'
            || msg.method === 'resolve_node_formula'
            || msg.method === 'set_model' || msg.method === 'restore_model'
            || msg.method === 'load_example_model') {
            await ensureFormulaSources();
        }
        if (msg.method === 'check_formula' || msg.method === 'evaluate'
            || msg.method === 'resolve_node_formula') {
            await ensureBnSources();
        }
        if (msg.method === 'evaluate'
            || msg.method === 'resolve_node_formula') {
            await ensureModelCheckerSources();
        }
        const res = await bnDispatch(JSON.stringify(msg));
        const text = Array.isArray(res) ? res[0] : res;
        // the file write stays on the host: the Lua service kept the
        // model in memory, here it is also persisted
        if (fs && msg.method === 'set_model'
                 && msg.model && typeof msg.model === 'object') {
            fs.writeFileSync(MODEL_FILE,
                             JSON.stringify(msg.model, null, 2));
        }
        return JSON.parse(text);
    }

    function createSession(write) {
        return {
            send: write,
            async onMessage(raw) {
                let msg;
                try { msg = JSON.parse(raw); }
                catch {
                    write(JSON.stringify(
                        {method: 'error', reason: 'invalid json'}));
                    return;
                }
                try {
                    write(JSON.stringify(await dispatch(msg)));
                } catch (err) {
                    write(JSON.stringify(
                        {method: 'error',
                         reason: String(err && err.message || err)}));
                }
            },
            close() {},
        };
    }

    return { createSession, dispatch, lua };
}
