# BayesL — iFS 2027 Artifact

Anonymous artifact accompanying the iFS 2027 submission
*“BayesL: A Logic for the Verification of Bayesian Networks”*.

## Interactive demonstrator

**[▶ Launch the demonstrator](https://bnchecker27.github.io/ifs27-artifact/gui/web/index.html)**

Runs entirely in your browser (WebAssembly; a one-time download of
about 3 MB). No installation, no server, no data leaves your machine.
Tested with current Chrome, Firefox and Safari.

## Downloading the artifact

- **Zip archive:** [download
  `main.zip`](https://github.com/bnchecker27/ifs27-artifact/archive/refs/heads/main.zip)
  (or use the green *Code → Download ZIP* button above)
- **Git:** `git clone https://github.com/bnchecker27/ifs27-artifact.git`

## Reproducing the experiments

See `README.txt` — it contains a getting-started guide with a smoke
test and step-by-step instructions for regenerating all experiment
tables reported in the paper and its appendix. The short version
(needs Docker + make):

```
make docker-load    # load the pre-built image
make check          # smoke test (< 5 min)
make tables         # regenerate the paper's table fragments
make experiments    # full re-run of all experiments (hours)
```

Pre-computed results for comparison ship in
`overleaf/experiments/results.csv`.

## Running the demonstrator locally (optional)

The hosted demo above serves this repository — running it locally is
equivalent and only needs a static file server at the repository root:

```
python3 -m http.server 8000
# then open http://localhost:8000/gui/web/index.html
```

## License

Provided for peer-review evaluation only — see `LICENSE`.
