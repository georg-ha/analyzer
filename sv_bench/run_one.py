#!/usr/bin/env python3
"""Run goblint on one (config, task, property) triple and write a JSON result."""

import argparse
import json
import re
import subprocess
import tempfile
import time
from pathlib import Path

SVCOMP_RESULT_RE  = re.compile(r"SV-COMP result: (.+)")
SOLVER_START_RE   = re.compile(r"Solver start: (\d+)")
SOLVER_END_RE     = re.compile(r"Solver end: (\d+)")
RHS_EVALS_RE      = re.compile(r"RHS: (\d+)")

# Prevent yaml from coercing bare true/false to Python bools
import yaml
class _Loader(yaml.SafeLoader):
    pass
_Loader.add_constructor(
    "tag:yaml.org,2002:bool",
    lambda loader, node: loader.construct_scalar(node),
)


def task_key(task_file: Path, sv_benchmarks: Path) -> str:
    try:
        rel = task_file.resolve().relative_to(sv_benchmarks.resolve())
        return str(rel)
    except ValueError:
        return str(task_file)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--goblint", required=True)
    parser.add_argument("--base-config", nargs="*", default=[])
    parser.add_argument("--config", required=True)
    parser.add_argument("--task", required=True)
    parser.add_argument("--property-file", required=True)
    parser.add_argument("--expected", required=True)
    parser.add_argument("--sv-benchmarks", required=True)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--sources", default="")
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    task_file = Path(args.task)
    config = Path(args.config)
    prop_file = Path(args.property_file)
    sv_benchmarks = Path(args.sv_benchmarks)

    with task_file.open() as f:
        task = yaml.load(f, Loader=_Loader)
    input_file = task_file.parent / task["input_files"]

    base_config_label = "__".join(Path(b).stem for b in args.base_config)

    cmd = [args.goblint]
    for b in args.base_config:
        cmd += ["--conf", str(Path(b).resolve())]
    cmd += [
        "--conf", str(config),
        "--set", "ana.specification", str(prop_file.resolve()),
        str(input_file),
    ]

    timed_out = False
    returned = "unknown"
    solver_walltime = None
    rhs_evals = None
    t0 = time.monotonic()
    with tempfile.TemporaryDirectory() as tmpdir:
        full_cmd = cmd + ["--set", "goblint-dir", tmpdir]
        try:
            result = subprocess.run(full_cmd, capture_output=True, text=True, timeout=args.timeout)
            combined = result.stdout + result.stderr
            m = SVCOMP_RESULT_RE.search(combined)
            if m:
                returned = m.group(1).strip()
            ms = SOLVER_START_RE.search(combined)
            me = SOLVER_END_RE.search(combined)
            if ms and me:
                solver_walltime = round((int(me.group(1)) - int(ms.group(1))) / 1000, 3)
            mr = RHS_EVALS_RE.search(combined)
            if mr:
                rhs_evals = int(mr.group(1))
        except subprocess.TimeoutExpired:
            timed_out = True
    runtime = round(time.monotonic() - t0, 2)

    row = {
        "base_config": base_config_label,
        "config": config.name,
        "task": task_key(task_file, sv_benchmarks),
        "property": prop_file.stem,
        "expected": args.expected,
        "returned": returned,
        "timeout": timed_out,
        "runtime": runtime,
        "solver_walltime": solver_walltime,
        "rhs_evals": rhs_evals,
        "sources": args.sources,
    }

    Path(args.output).write_text(json.dumps(row))


if __name__ == "__main__":
    main()
