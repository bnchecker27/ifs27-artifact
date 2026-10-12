/**
 * validate.mjs — model validation for the RPM server.
 *
 * Checks a client-supplied Bayesian-network model and returns ALL
 * problems found (the BIF parser stops at the first error; here the
 * client wants to mark every problem at once).
 *
 * Model shape:
 *   { nodes: [{id, name, desc, x, y, outcomes: [str...],
 *              cpt: [[p...], ...]}],            // rows x outcome columns
 *     edges: [{from, to}] }                     // node ids
 *
 * Problem shape:
 *   { sev: 'error'|'warning', key, node?, row?, col?, cell?, msg }
 * `node` is a node id; `cell` is the flat 1-based CPT cell index
 * (row * outcomes + col) so the client can mark the exact cell.
 */

const TOL = 1e-6;

export function validateModel(model) {
	const problems = [];
	const err = (key, msg, extra) =>
		problems.push({ sev: 'error', key, msg, ...(extra || {}) });
	const warn = (key, msg, extra) =>
		problems.push({ sev: 'warning', key, msg, ...(extra || {}) });

	if (!model || typeof model !== 'object') {
		err('no_model', 'no model received');
		return problems;
	}
	const nodes = Array.isArray(model.nodes) ? model.nodes : [];
	const edges = Array.isArray(model.edges) ? model.edges : [];

	const byId = new Map();
	for (const n of nodes) {
		if (n && n.id !== undefined && n.id !== null && !byId.has(Number(n.id))) {
			byId.set(Number(n.id), n);
		}
	}

	// --- node names and outcome labels --------------------------------
	const nameSeen = new Map(); // name -> first node id
	for (const n of nodes) {
		const id = Number(n.id);
		const name = typeof n.name === 'string' ? n.name.trim() : '';
		if (name === '') {
			err('empty_name', 'a node has no name', { node: id });
		} else if (nameSeen.has(name)) {
			err('duplicate_name',
				`duplicate node name "${name}"`, { node: id });
			err('duplicate_name',
				`duplicate node name "${name}"`, { node: nameSeen.get(name) });
		} else {
			nameSeen.set(name, id);
		}

		const outs = Array.isArray(n.outcomes) ? n.outcomes : [];
		if (outs.length === 0) {
			err('no_outcomes',
				`node "${name}" has no outcome values`, { node: id });
		}
		const vseen = new Set();
		for (const v of outs) {
			const sv = String(v);
			if (vseen.has(sv)) {
				err('duplicate_value',
					`node "${name}" has duplicate outcome "${sv}"`,
					{ node: id });
			}
			vseen.add(sv);
		}
	}

	// --- edges ---------------------------------------------------------
	const parents = new Map(); // child id -> [parent ids]
	for (const e of edges) {
		const from = Number(e && e.from);
		const to = Number(e && e.to);
		if (from === to) {
			err('self_loop', `node ${from} has an edge to itself`,
				{ node: from });
		}
		if (!byId.has(from) || !byId.has(to)) {
			err('dangling_edge',
				`edge ${from} -> ${to} references an unknown node`,
				{ node: byId.has(from) ? from : to });
			continue;
		}
		if (!parents.has(to)) parents.set(to, []);
		parents.get(to).push(from);
	}

	// --- directed cycles -----------------------------------------------
	{
		const adj = new Map();
		for (const e of edges) {
			const from = Number(e.from), to = Number(e.to);
			if (!adj.has(from)) adj.set(from, []);
			adj.get(from).push(to);
		}
		const state = new Map(); // 0 unseen, 1 in stack, 2 done
		const inCycle = new Set();
		const stack = [];
		const dfs = (u) => {
			state.set(u, 1);
			stack.push(u);
			for (const v of adj.get(u) || []) {
				if (state.get(v) === 1) {
					for (const w of stack.slice(stack.indexOf(v))) {
						inCycle.add(w);
					}
				} else if (!state.get(v)) {
					dfs(v);
				}
			}
			stack.pop();
			state.set(u, 2);
		};
		for (const n of nodes) {
			const u = Number(n.id);
			if (!state.get(u)) dfs(u);
		}
		for (const u of inCycle) {
			err('cycle', `node ${u} is part of a directed cycle`,
				{ node: u });
		}
	}

	// --- CPTs ------------------------------------------------------------
	for (const n of nodes) {
		const id = Number(n.id);
		const name = String(n.name ?? '');
		const nv = Array.isArray(n.outcomes) ? n.outcomes.length : 0;
		const plist = parents.get(id) || [];
		let expected = 1;
		for (const p of plist) {
			const pn = byId.get(p);
			const k = pn && Array.isArray(pn.outcomes)
				? pn.outcomes.length : 1;
			expected *= Math.max(1, k);
		}
		const cpt = Array.isArray(n.cpt) ? n.cpt : [];
		if (cpt.length === 0) {
			err('missing_cpt',
				`node "${name}" has no probability table`, { node: id });
			continue;
		}
		if (cpt.length !== expected) {
			err('cpt_row_count',
				`node "${name}": CPT has ${cpt.length} rows, ` +
				`expected ${expected} (product of parent outcomes)`,
				{ node: id });
		}
		for (let r = 0; r < cpt.length; r++) {
			const row = cpt[r];
			if (!Array.isArray(row)) {
				err('cpt_row_width',
					`node "${name}" row ${r + 1} is not a list`,
					{ node: id, row: r + 1 });
				continue;
			}
			if (row.length !== nv) {
				err('cpt_row_width',
					`node "${name}" row ${r + 1} has ${row.length} ` +
					`entries, expected ${nv}`,
					{ node: id, row: r + 1 });
			}
			let sum = 0;
			let allNum = true;
			for (let c = 0; c < row.length; c++) {
				const v = row[c];
				const cell = r * nv + c + 1;
				const num = typeof v === 'number' ? v
					: (typeof v === 'string' && v.trim() !== ''
						? Number(v) : NaN);
				if (Number.isNaN(num)) {
					// symbolic values (fractions, polynomials) are
					// allowed — they just cannot be checked yet
					warn('cell_not_numeric',
						`node "${name}" row ${r + 1} col ${c + 1}: ` +
						`"${String(v)}" is not a number — cannot verify`,
						{ node: id, row: r + 1, col: c + 1, cell });
					allNum = false;
				} else {
					if (num < 0 || num > 1) {
						err('cell_out_of_range',
							`node "${name}" row ${r + 1} col ${c + 1}: ` +
							`${num} outside [0,1]`,
							{ node: id, row: r + 1, col: c + 1, cell });
					}
					sum += num;
				}
			}
			if (allNum && row.length === nv && Math.abs(sum - 1) > TOL) {
				err('row_sum',
					`node "${name}" row ${r + 1} probabilities sum ` +
					`to ${+sum.toFixed(6)}, not 1`,
					{ node: id, row: r + 1 });
			}
		}
	}

	return problems;
}
