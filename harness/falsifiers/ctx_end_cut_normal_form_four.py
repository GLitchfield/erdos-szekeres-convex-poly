#!/usr/bin/env python3
"""Falsifier for the restricted end-cut normal form (Workstream B node
ctx_bound_attained_by_end_cut_of_four_le): for every well-formed context with at least two
child runs and both global parameters a, u >= 4, the bound is attained by a cut that isolates
the first or the last child position (either side, some coupling). The unrestricted statement
fails at a = 3 and, by the cap/cup mirror, at u = 3 (ctx_bound_attained_by_end_cut_counterexample);
every case here has a, u >= 4, including the mirror (5,4,5).

First replays two R19 literal witnesses, whose hypotheses and end-cut gaps have
independent compiling Lean receipts. The historical generated scan covers only
two external levels and misses both witnesses. The fixed regressions use the
shared compiled zero-child recurrence and singleton-cut enumerator; their
computed values remain diagnostic, rather than substitutes for those receipts.
If the regressions do not refute the statement, runs the historical literal
Lean-recursion scan on a few cases.
Exit 0: no violation; exit 2: a context whose bound needs an interior block (witness in --out).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.research.context_bound import compiled_evaluator
from harness.research.singleton_cuts import singleton_cut_values


def regression_results(node):
    """Replay two fixed, independently Lean-certified WellFormed contexts."""
    candidates = [
        {
            "a": 4, "u": 4, "k": 5,
            "word": ((3, "upper"), (4, "lower"), "S", "S",
                     (1, "lower"), (2, "upper"), "S", "S"),
            "maxima": (1, 1, 1, 1), "chosen": "lower",
            "lean_receipt": "9159d9e9c8b436a7edd362410be34693c221562de3d85dcfca000cbb2c7ee3f5",
        },
        {
            "a": 5, "u": 5, "k": 6,
            "word": ("S", "S", "S", (1, "lower"),
                     (3, "lower"), (2, "lower"), "S"),
            "maxima": (1, 1, 1), "chosen": "lower",
            "lean_receipt": "37353e1f739a6742ee72aa641913fdcf267f1bdadc569e67d87be88a4f097f51",
        },
    ]
    start = time.monotonic()
    checked = []
    violations = []
    for done, row in enumerate(candidates, 1):
        positions = [i for i, token in enumerate(row["word"]) if token == "S"]
        ends = {positions[0], positions[-1]}
        evaluate = compiled_evaluator(row["a"], row["u"], row["k"], persistent=True)
        try:
            bound = evaluate(row["word"], row["maxima"])
            end_cuts = [choice for choice in singleton_cut_values(evaluate, row)
                        if choice[1] in ends]
        finally:
            evaluate.close()
        best = max(choice[0] for choice in end_cuts)
        if best > bound:
            raise ValueError("end singleton exceeds the interval recurrence")
        result = {**row, "bound": bound, "best_end": best, "end_cuts": end_cuts}
        checked.append(result)
        if best < bound:
            violations.append(result)
        print(json.dumps({"regression": done, "total": len(candidates),
                          "bound": bound, "best_end": best,
                          "seconds": time.monotonic() - start}),
              file=sys.stderr, flush=True)
    return {
        "node": node, "recursion": "context-bound-zero-children-c-v1",
        "scope": "two-fixed-R19-WellFormed-context-regressions-v1",
        "diagnostic_only": True, "checked": checked, "violations": violations,
        "seconds": time.monotonic() - start,
    }


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
    ap.add_argument("--regressions-only", action="store_true")
    a = ap.parse_args()
    regressions = regression_results(a.node)
    if regressions["violations"] or a.regressions_only:
        if a.out:
            Path(a.out).parent.mkdir(parents=True, exist_ok=True)
            Path(a.out).write_text(json.dumps(regressions, indent=1) + "\n")
        return 2 if regressions["violations"] else 0
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
