#!/usr/bin/env python3
"""Falsifier for the end-cut normal form (Workstream B node ctx_bound_attained_by_end_cut):
for every well-formed context with at least two child runs, the bound is attained by a cut
that isolates the first or the last child position (either side, some coupling).

Runs scripts/decomposable_end_cut_normal_form.py (literal Lean recursion) on a few cases and
fails when some context with a nonzero bound has every end cut strictly below the bound.
Exit 0: no violation; exit 2: a context whose bound needs an interior block (witness in --out).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset")
    ap.add_argument("--out")
    ap.add_argument("--node")
    ap.add_argument("--statement")
    ap.add_argument("--cases", default="4,4,5;4,5,5;5,5,5;4,5,6;5,5,6")
    ap.add_argument("--s-max", type=int, default=4)
    ap.add_argument("--e-max", type=int, default=2)
    ap.add_argument("--levels", type=int, default=2)
    a = ap.parse_args()
    tmp = Path(a.dataset or ROOT / "harness" / "dataset") / "ctx_end_cut_normal_form"
    tmp.mkdir(parents=True, exist_ok=True)
    summary = {"node": a.node, "recursion": "lean", "cases": {}}
    violations = []
    for case in a.cases.split(";"):
        out = tmp / f"endcut-{case.replace(',', '')}-s{a.s_max}e{a.e_max}l{a.levels}.json"
        proc = subprocess.run([sys.executable, str(ROOT / "scripts" / "decomposable_end_cut_normal_form.py"), "--case", case,
                               "--s-max", str(a.s_max), "--e-max", str(a.e_max), "--levels", str(a.levels),
                               "--cache-size", "1500000", "--output", str(out)], capture_output=True, text=True, cwd=ROOT)
        if proc.returncode != 0:
            print(proc.stderr[-2000:], file=sys.stderr)
            return 1
        d = json.loads(out.read_text())
        s = d["stats"]
        nonzero = s.get("contexts", 0) - s.get("zero_bound", 0)
        summary["cases"][case] = {"contexts": s.get("contexts", 0), "nonzero": nonzero, "end_attains": s.get("end_attains", 0)}
        if s.get("end_attains", 0) < nonzero:
            violations.append({"case": case, "examples": d["examples"].get("boundary_only", [])[:5] + d["examples"].get("interior_only", [])[:5]})
        print(json.dumps({"case": case, **summary["cases"][case]}), file=sys.stderr, flush=True)
    summary["violations"] = violations
    if a.out:
        Path(a.out).write_text(json.dumps(summary, indent=1) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
