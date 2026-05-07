# sv_bench

Benchmark harness for running goblint on SV-COMP tasks.

## Setup

```
uv sync
```

## Configure

Edit `bench.yaml` to set the goblint binary, configs, tasks, and timeout.

## Run

```
uv run snakemake --cores 8
```

This produces `results/combined.csv`. Jobs are skipped on re-run if already complete.

## Evaluate

Run the snakemake step first, then open the notebook:

```
uv run marimo edit --watch evaluate.py
```

## Result data formats

**`results/<base_config>__<config>/<task_key>/<property>.json`** — one file per run.
- `task_key` encodes the task path relative to `sv_benchmarks`, with `/` replaced by `__`.
- Fields: see combined.csv below.

**`results/combined.csv`** — all runs aggregated into one file.

| Column | Description |
|---|---|
| `base_config` | Base config stem (e.g. `svcomp25`), empty if none |
| `config` | Solver config filename (e.g. `wbu.json`) |
| `task` | Task path relative to `sv_benchmarks` |
| `property` | Property stem (e.g. `unreach-call`) |
| `expected` | Expected verdict (`true` / `false`) |
| `returned` | Verdict returned by goblint, or `unknown` |
| `timeout` | `True` if the run hit the timeout |
| `runtime` | Wall time of the full goblint process (seconds) |
| `solver_walltime` | Time between solver start and end events (seconds), `NaN` if not logged |
| `rhs_evals` | Number of RHS evaluations by the solver, `NaN` if not logged |
| `sources` | `\|`-separated list of `.set` files the task was drawn from; empty if specified directly |
