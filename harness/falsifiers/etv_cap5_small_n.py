#!/usr/bin/env python3
"""Falsifier for the Erdős–Tuza–Valtr cap-parameter-5 conjecture node (Workstream C).

The node says: for every n >= 5, every sweep-realizable coloring on more than
decomposableThreshold 5 n n vertices contains a 5-cap, an n-cup, or a strong
n-set.  At the signotope tier (one-change colorings, a superset of the
realizable ones) this is decided by the SAT instance of experiment 0112
(scripts/generate_etv_signotope_sat.py, unanchored: anchoring is unsound for
cap/cup constraints).  For each n in --n (default 5 6, the values that solve in
seconds) the script decides N = threshold + 1 and, as an encoding gate,
N = threshold (which must be SAT: the threshold is attained by the
Erdős–Szekeres construction).

Exit 0: every threshold + 1 instance is UNSAT (the conjecture holds at these n
even at the abstract tier).  Exit 2: a threshold + 1 instance is SAT and the
witness has been certified realizable (never automatic: only with
--accept-signotope, for a human who has checked realizability separately).
Exit 3: a threshold + 1 instance is SAT but its realizability is undetermined
(the witness coloring is written to --out for a realizability check), a gate
fails, or the solver is unavailable.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import generate_etv_signotope_sat as etv  # noqa: E402


def cadical_path() -> str | None:
    for cand in (os.environ.get("CADICAL"), ROOT / "scripts" / "toolchain" / "cadical"):
        if cand and Path(cand).exists():
            return str(cand)
    try:
        prefix = subprocess.run(["lean", "--print-prefix"], capture_output=True, text=True, check=True).stdout.strip()
        p = Path(prefix) / "bin" / "cadical"
        if p.exists():
            return str(p)
    except (OSError, subprocess.CalledProcessError):
        pass
    import shutil
    return shutil.which("cadical")


def decomposable_threshold(a: int, u: int, k: int) -> int:
    """Mirror of ErdosSzekeres.decomposableThreshold (Decomposable.lean)."""
    if a == 1 or u == 1:
        return 0
    if a + u <= k + 3:
        return math.comb(a + u - 4, a - 2)
    return sum(math.comb(k - 2, j) for j in range(k - a, u - 2 + 1))


def decide(N: int, n: int, cad: str) -> dict:
    var, records = etv.generate(N, n, 5, n, anchored=False)
    cnf = etv.dimacs(len(var), records)
    started = time.time()
    verdict, model = etv.solve(cnf, Path(cad))
    entry = {"N": N, "n": n, "a": 5, "b": n, "verdict": verdict, "variables": len(var),
             "clauses": len(records), "seconds": round(time.time() - started, 2)}
    if model is not None:
        entry["model_check"] = etv.check_model(var, model, N, 5, n, n)
        entry["left_turn_triples"] = sorted(t for t, v in var.items() if v in model)
    return entry


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset")
    ap.add_argument("--out")
    ap.add_argument("--node")
    ap.add_argument("--statement")
    ap.add_argument("--n", type=int, action="append", help="polygon sizes n (default 5 6)")
    ap.add_argument("--accept-signotope", action="store_true",
                    help="treat a signotope-tier SAT witness as a counterexample (only after a realizability check)")
    a = ap.parse_args()
    ns = a.n or [5, 6]
    cad = cadical_path()
    if not cad:
        print("cadical not found", file=sys.stderr)
        return 3
    results = []
    counterexamples = []
    undetermined = []
    gate_failures = []
    for n in ns:
        threshold = decomposable_threshold(5, n, n)
        gate = decide(threshold, n, cad)
        gate["role"] = "gate: threshold must be attained (SAT)"
        results.append(gate)
        if gate["verdict"] != "SAT" or not gate.get("model_check", {}).get("valid"):
            gate_failures.append(gate)
        main_entry = decide(threshold + 1, n, cad)
        main_entry["role"] = "conjecture: threshold + 1 must be UNSAT"
        results.append(main_entry)
        if main_entry["verdict"] == "SAT":
            if not main_entry.get("model_check", {}).get("valid"):
                gate_failures.append(main_entry)
            elif a.accept_signotope:
                counterexamples.append(main_entry)
            else:
                undetermined.append(main_entry)
        elif main_entry["verdict"] != "UNSAT":
            gate_failures.append(main_entry)
        print(json.dumps({k: v for k, v in main_entry.items() if k != "left_turn_triples"}), file=sys.stderr, flush=True)
    summary = {"node": a.node, "n_values": ns, "results": [
        {k: v for k, v in r.items() if k != "left_turn_triples" or r["role"].startswith("conjecture")}
        for r in results],
        "counterexamples": counterexamples, "undetermined": undetermined, "gate_failures": gate_failures}
    if a.out:
        Path(a.out).write_text(json.dumps(summary, indent=1))
    print(json.dumps({"n_values": ns, "counterexamples": len(counterexamples), "undetermined": len(undetermined),
                      "gate_failures": len(gate_failures)}), file=sys.stderr)
    if counterexamples:
        return 2
    if undetermined:
        print("signotope-tier SAT at threshold + 1: realizability undetermined; witness in --out", file=sys.stderr)
        return 3
    if gate_failures:
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
