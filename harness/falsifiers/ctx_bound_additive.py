#!/usr/bin/env python3
"""Falsifier for the additivity conjecture of the context recursion (Workstream B node
ctx_bound_additive): scripts/decomposable_additivity_test.py with Lean's interval cuts on the
abstract contexts of a few cases (up to four child letters, two external levels).
Zero-valued children and parents are included, as in the Lean statement.
Exit 0: no violation; exit 2: a context and partition whose two part bounds exceed the
parent's bound (witness in --out); other: error.
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
    ap.add_argument("--cases", default="3,3,3;3,3,4;4,4,5;4,5,5;5,4,5;4,5,6")
    ap.add_argument("--s-max", type=int, default=4)
    ap.add_argument("--e-max", type=int, default=2)
    ap.add_argument("--levels", type=int, default=2)
    a = ap.parse_args()
    tmp = Path(a.dataset or ROOT / "harness" / "dataset") / "ctx_bound_additive"
    tmp.mkdir(parents=True, exist_ok=True)
    summary = {"node": a.node, "recursion": "lean", "cases": {}}
    violations = []
    for case in a.cases.split(";"):
        out = tmp / f"add-{case.replace(',', '')}-s{a.s_max}e{a.e_max}l{a.levels}-lean.json"
        proc = subprocess.run([sys.executable, str(ROOT / "scripts" / "decomposable_additivity_test.py"), "--case", case,
                               "--s-max", str(a.s_max), "--e-max", str(a.e_max), "--levels", str(a.levels),
                               "--recursion", "lean", "--cache-size", "1500000", "--output", str(out)],
                              capture_output=True, text=True, cwd=ROOT)
        if proc.returncode != 0:
            print(proc.stderr[-2000:], file=sys.stderr)
            return 3
        d = json.loads(out.read_text())
        summary["cases"][case] = d["stats"]
        if d["stats"]["violations"]:
            violations.append({"case": case, "examples": d["violations"][:10]})
        print(json.dumps({"case": case, **{k: v for k, v in d["stats"].items() if k != "slack_histogram"}}), file=sys.stderr, flush=True)
    summary["violations"] = violations
    if a.out:
        Path(a.out).write_text(json.dumps(summary, indent=1))
    return 2 if violations else 0


if __name__ == "__main__":
    sys.exit(main())
