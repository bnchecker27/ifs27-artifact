BayesL Model Checker — iFS 2027 Artifact
========================================

This package accompanies the iFS 2027 submission "BayesL: A Logic for
the Verification of Bayesian Networks".  It contains everything needed
to (1) reproduce the experimental tables reported in the paper and its
appendix, (2) re-run the experiments from scratch, and (3) interactively
explore the BayesL language and the benchmark models in a browser GUI.

The artefact is intended to demonstrate the practical usability of the
BayesL logic: besides the command-line model checker it ships the
interactive demonstrator discussed in the paper, which lets researchers
edit models, compose properties, and experiment with the case study and
benchmarks from the paper.

Note: Some of the code and other materials in this artifact were
produced with LLM assistance and reviewed by the authors, who take full
responsibility for all content.

The package is self-contained: the model checker and its LuaJIT
environment run inside a pre-built multi-architecture Docker image
(linux/amd64 + linux/arm64); no LuaJIT, Lua, or Python installation is
required on the host system.  The GUI is delivered as a pre-built
WebAssembly application and runs entirely in the browser, while all
inference still runs natively in the Docker container (see "BROWSER
GUI" below).


CONTENTS
--------
- README.txt:             this file
- Makefile:               entry points (check / experiments / tables / gui)
- Dockerfile:             definition of the runtime image, for reference
- bayesian-luajit.tar:    pre-built Docker image (amd64 + arm64)
- patches/:               source patch applied to lpeg in the image build
- main.lua:               command-line entry point of the model checker
- run_experiments.lua:    experiment driver (reads experiments.csv)
- create_summary_table.lua: regenerates the paper's LaTeX table fragments
- bayesian_network/:      BIF parser and network data structures
- lib/:                   utility libraries
- logic/:                 BayesL formula parser
- model_checker/:         variable-elimination and sampling solvers
- locales/:               error messages
- models/:                the eight benchmark BNs used in the paper
                          (grades, insurance, pathfinder, andes, pigs,
                          link, munin — bnlearn — and the win95 case
                          study network)
- overleaf/experiments/:  the paper's experiment definitions
                          (experiments.csv), the pre-computed results
                          (results.csv), the table-selection file
                          (chosen.csv), per-model descriptions, and the
                          generated LaTeX fragments included by the paper
- server/httpd.lua:       HTTP+RPC server used by the browser GUI
- server/lua/:            checker service, validation, JSON codec, and
                          the example models/properties shown in the GUI
- gui/web/:               pre-built browser GUI (WebAssembly build)


GETTING STARTED (smoke test, < 5 minutes)
-----------------------------------------
Requirements: Docker (any recent version; Buildx only needed to rebuild
the image), and `make`.  For PDF table compilation you additionally need
a TeX installation (pdflatex, bibtex); the table *fragments* themselves
are generated inside the container.

1. Unpack the archive and enter the directory:

     unzip bayesl-ifs-artifact.zip -d bayesl-ifs
     cd bayesl-ifs

2. Load the pre-built Docker image:

     make docker-load          # or: docker load < bayesian-luajit.tar

3. Smoke test — one property against the Grades benchmark:

     make check

   Expected output (exact number formatting may differ slightly):

       true

   i.e. the probability of a strong letter given a high grade exceeds
   0.7.  You can also run the checker directly, e.g.:

     docker run --rm -v "$(pwd)":/app bayesian-luajit \
         --model models/win95.bif \
         --property 'P(Problem1=No__Local_printer_)>=0.5'

   Properties follow the paper's syntax: P(phi|psi) >= p,
   MAP(X,Y|phi), MPE(phi), IDP(X,Y|Z), INFL(X,Y|Z), Boolean
   connectives (!, &&, || written !, ∧, ∨ or ASCII equivalents), CPT
   updates "f[X = x | E = e ↦ q]", and arithmetic on probability terms.


BROWSER GUI (interactive demonstrator)
--------------------------------------
     make gui

then open

     http://localhost:8082

in a browser.  The GUI is the demonstrator referred to in the paper: it
visualises the Bayesian network, offers the paper's eight benchmark
models under the model drop-down (including the Windows 95 case study),
and lists each model's paper properties under the formula drop-down.
Models can be edited graphically and formulas interactively; hovering a
node or a subformula shows its (conditional) marginal distribution, and
syntax errors are annotated in place — intended to demonstrate the
practical usability of the logic and to let researchers experiment.

Architecture: the user interface (WebAssembly build of the shared
Nuklear/Lua UI) runs in the browser; every query is sent over HTTP to
the native LuaJIT model checker running inside the container, so no
inference code executes in the browser.  Ctrl-C (or `docker stop`) ends
the session.  The GUI keeps the current model in server/model.json.

Use `GUI_PORT=<n> make gui` to serve on a different port.  Outside
Docker, the same GUI can be run with a system LuaJIT:

     luajit server/httpd.lua 8082

(LuaJIT plus the lpeg shared library is required; inside Docker nothing
of the sort is needed.)


REPRODUCING THE PAPER'S TABLES
------------------------------
The package ships the pre-computed results in
overleaf/experiments/results.csv together with the experiment
definitions (experiments.csv) and the per-model selections used for the
main paper table (chosen.csv).

Regenerate all LaTeX table fragments (the per-model tables of the
appendix, the summary fragments, the model overview table, and the
win95 case-study table):

     make tables

This rewrites the *.tex fragments under overleaf/experiments/; they are
the exact files \input'ed by the paper.  To compile the standalone
table documents (requires a host TeX installation):

     cd overleaf/experiments
     pdflatex -interaction=nonstopmode summary_table_full.tex
     bibtex summary_table_full
     pdflatex -interaction=nonstopmode summary_table_full.tex
     pdflatex -interaction=nonstopmode summary_table_full.tex

(and likewise for summary_table.tex, which contains the main-paper
selection only.)


RE-RUNNING THE EXPERIMENTS
--------------------------
Each experiment applies both solving engines to the property:
variable elimination and rejection sampling with 10^7 samples and seed
42, each repeated 10 times; reported runtimes are averages.

Quick verification (one repetition per experiment, still some time for
the large models):

     make experiments-single

Full reproduction (10 repetitions; may take several hours):

     make experiments

Results append to overleaf/experiments/results.csv; run `make tables`
afterwards to regenerate the LaTeX.  To restart completely, delete that
file first.

Note on timing: exact runtimes depend on the host; qualitative ordering
(in particular the higher cost of MAP/MPE explanation queries on the
largest models) reproduces.  Sampling solvers are deterministic given
the fixed seed; variable-elimination times are hardware-dependent.


SUPPORTED CLAIMS
----------------
- The artefact reproduces all experimental tables of the paper
  (Section on experiments and the appendix): per-model property tables
  for grades, insurance, pathfinder, andes, pigs, link, munin, and the
  Windows 95 case-study table, for both the variable-elimination and
  the rejection-sampling engines.
- The browser GUI demonstrates the tool's practical usability on every
  model and property of the paper and permits free experimentation.
- The artefact contains exactly the language presented in the paper.
  Experimental extensions not discussed in the paper (LET bindings,
  conditional terms, DIST/RENAME/MUX/distribution literals, moment
  queries, and random-variable arithmetic) are not part of this
  package.  The remaining optional feature flags (--features
  marginal,chart,numval,arith) enable the GUI's marginal-distribution
  display and numeric-valued outcomes used by the pigs/link benchmark
  models.

LIMITS
------
- Exact runtime figures are not hardware-portable; reproduce ordering
  and qualitative findings, not identical numbers.
- Whole-network MPE queries on the largest models (munin, link) can
  still exceed the available memory; such queries are not part of the
  paper's benchmark set.  The checker caps runaway computations and
  reports a resource limit instead of crashing, and the GUI still
  loads these models fine.
- The GUI uses the exact (variable-elimination and structural) solvers
  only; the sampling engine is exercised by the benchmark protocol
  (`make experiments`) and can be enabled explicitly on the command
  line.  A query exceeding the checker's resource limits reports an
  error instead of blocking the server.


ANONYMITY
---------
This package is anonymised: it carries no author names, institution
identifiers, repository URLs, or local paths.


CLEANUP
-------
     make clean          # removes the GUI's saved model state
     docker rmi bayesian-luajit
