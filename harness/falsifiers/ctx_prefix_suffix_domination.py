#!/usr/bin/env python3
"""Falsifier for prefix/suffix domination in every context (Workstream B node
ctx_bound_prefix_suffix_domination): every partition of a well-formed context that is not
itself a prefix or suffix cut, in either orientation and at any admissible coupling d, is
dominated by a prefix or suffix cut in the same orientation at some admissible coupling d'.

Runs scripts/decomposable_exchange_test.py --runs any --all-partitions (literal Lean recursion)
on a few cases and fails when the candidate `prefix_suffix_same_orientation` has a failure.
Exit 0: no violation; exit 2: an undominated partition (witness in --out); other: error.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = "prefix_suffix_same_orientation"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset")
    ap.add_argument("--out")
    ap.add_argument("--node")
    ap.add_argument("--statement")
    ap.add_argument("--cases", default="4,4,5;4,5,5;5,4,5;5,5,5;4,5,6;5,5,6")
    ap.add_argument("--s-max", type=int, default=4)
    ap.add_argument("--e-max", type=int, default=2)
    ap.add_argument("--levels", type=int, default=2)
    a = ap.parse_args()
    tmp = Path(a.dataset or ROOT / "harness" / "dataset") / "ctx_prefix_suffix_domination"
    tmp.mkdir(parents=True, exist_ok=True)
    summary = {"node": a.node, "candidate": CANDIDATE, "recursion": "lean", "runs": "any", "partitions": "all but prefix/suffix cuts", "cases": {}}
    violations = []
    for case in a.cases.split(";"):
        out = tmp / f"domination-{case.replace(',', '')}-s{a.s_max}e{a.e_max}l{a.levels}.json"
        proc = subprocess.run([sys.executable, str(ROOT / "scripts" / "decomposable_exchange_test.py"), "--case", case,
                               "--s-max", str(a.s_max), "--e-max", str(a.e_max), "--levels", str(a.levels),
                               "--runs", "any", "--all-partitions", "--cache-size", "1500000", "--output", str(out)],
                              capture_output=True, text=True, cwd=ROOT)
        if proc.returncode != 0:
            print(proc.stderr[-2000:], file=sys.stderr)
            return 1
        d = json.loads(out.read_text())
        stats = d["stats"]
        summary["cases"][case] = {"contexts": stats["contexts"], "splits": stats["splits"], "failures": stats["failures"][CANDIDATE]}
        if stats["failures"][CANDIDATE]:
            violations.append({"case": case, "examples": d["examples"][CANDIDATE][:5]})
        print(json.dumps({"case": case, **summary["cases"][case]}), file=sys.stderr, flush=True)
    summary["violations"] = violations
    if a.out:
        Path(a.out).write_text(json.dumps(summary, indent=1) + "\n")
    return 2 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
