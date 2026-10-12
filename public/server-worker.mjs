// The page appends its cache-busted index.js ?v= hash to this worker's
// URL; propagate it to the service module so the whole module chain is
// fetched fresh after each deploy.
const v = new URL(self.location.href).searchParams.get('v') || '';
const { createService } = await import(
	'../server/src/service.mjs' + (v ? '?v=' + v : ''));

const service = await createService(self);

const session = service.createSession(
	(json) => self.postMessage(JSON.parse(json))
);

// Tell the client that the worker has finished starting up and is ready
// to receive JSON protocol messages.
session.send(JSON.stringify({ method: 'ready' }));

self.onmessage = (e) => {
	session.onMessage(JSON.stringify(e.data));
};
