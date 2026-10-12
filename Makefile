# BayesL iFS artefact — build/run helpers.  Everything except LaTeX PDF
# compilation runs inside the packaged Docker image; no LuaJIT or other
# tooling is needed on the host.

DOCKER_IMAGE = bayesian-luajit
GUI_PORT = 8082

.PHONY: all docker-load check experiments experiments-single tables gui clean

all: docker-load

# Load the pre-built image (linux/amd64 + linux/arm64) into Docker.
docker-load:
	docker load < $(DOCKER_IMAGE).tar

# Smoke test: one model-checker query against the Grades benchmark.
check: docker-load
	docker run --rm -v $(CURDIR):/app $(DOCKER_IMAGE) \
		--model models/grades.bif \
		--property 'P(Letter=Strong|Grade=High)>=0.7'

# Re-run every experiment in overleaf/experiments/experiments.csv
# (10 repetitions per property/engine; several hours in total).
experiments: docker-load
	docker run --rm --entrypoint /usr/local/bin/luajit \
		-v $(CURDIR):/app $(DOCKER_IMAGE) run_experiments.lua

# Quick verification: one repetition per experiment only.
experiments-single: docker-load
	docker run --rm --entrypoint /usr/local/bin/luajit \
		-v $(CURDIR):/app $(DOCKER_IMAGE) \
		run_experiments.lua --single-run

# Regenerate the paper's LaTeX table fragments from
# overleaf/experiments/results.csv (writes summary_table_fragment_*.tex,
# property_descriptions_*.tex, model_table.tex, win95_case_table.tex).
tables: docker-load
	docker run --rm --entrypoint /usr/local/bin/luajit \
		-v $(CURDIR):/app $(DOCKER_IMAGE) create_summary_table.lua

# Browser GUI: serves gui/web + the JSON-RPC endpoint on
# http://localhost:$(GUI_PORT).  The UI runs in the browser; every query
# is answered by the native LuaJIT checker inside the container.
# Named container + restart policy: a heavy query can OOM-kill the
# luajit process (Docker SIGKILLs it); unless-stopped brings the server
# back instead of leaving the GUI dead.  `docker stop bayesl-gui` ends
# it; the leading `docker rm -f` also re-binds the mount after the
# staging tree has been recreated (a stale mount serves 404s).
gui: docker-load
	@echo "Starting BayesL demonstrator on http://localhost:$(GUI_PORT)"
	-docker rm -f bayesl-gui >/dev/null 2>&1 || true
	docker run --init --restart unless-stopped --name bayesl-gui \
		-p $(GUI_PORT):$(GUI_PORT) \
		-e BAYESL_BIND=0.0.0.0 \
		-e BAYESL_WEB_DIR=/app/gui/web \
		-e BAYESL_FEATURES=marginal,chart,numval \
		-v $(CURDIR):/app \
		--entrypoint /usr/local/bin/luajit $(DOCKER_IMAGE) \
		server/httpd.lua $(GUI_PORT)

clean:
	rm -f server/model.json
