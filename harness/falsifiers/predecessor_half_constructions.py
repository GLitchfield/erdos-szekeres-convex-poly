#!/usr/bin/env python3
"""Falsifier for the predecessor-half conjecture node (Workstream E).

Steps, cheapest first (``--steps`` selects; all run by default):

* ``constructions``: for each known extremal k-gon-free construction (the
  classical Erdős–Szekeres set and the Theorem-19 blow-ups of
  scripts/baek_balko_constructions.py) at k = 6, 7, a (k-1)-gon-free subset of
  at least half the points must exist (experiment 0108).
* ``interleaved``: deep-below unions of Erdős–Szekeres sets P(a,u) at k = 7
  (25 to 36 points, pruned to strong-7-free subsets where needed), tested in
  the abstract decomposable class, which is sweep-realizable
  (scripts/predecessor_half_interleaved_sets.py, experiment 0115).
* ``flips``: a short flip walk from every k = 7 construction, each new
  heptagon-free order type getting the half search
  (scripts/predecessor_half_perturbation_search.py, experiments 0113, 0115).
* ``cegar``: the signotope-tier search at k = 7 for an anchored one-change
  coloring on --cegar-n vertices with no strong 7-set and no strong-6-free
  half, counterexample-guided, within --cegar-seconds
  (scripts/predecessor_half_k7_cegar.py, experiment 0115); an abstract
  witness is reported as an error (exit 3) until its realizability is checked.

Exit 0 = no counterexample in any step, 2 = counterexample (witness in --out),
other = error.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPTS = ROOT / "scripts"


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


def run_script(argv, log_tail=2000):
    proc = subprocess.run([sys.executable] + [str(a) for a in argv], capture_output=True, text=True, cwd=ROOT)
    if proc.returncode not in (0, 2):
        print(proc.stderr[-log_tail:], file=sys.stderr)
    return proc


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset")
    ap.add_argument("--out")
    ap.add_argument("--node")
    ap.add_argument("--statement")
    ap.add_argument("--k", type=int, action="append", help="k values for the constructions step (default 6 7)")
    ap.add_argument("--steps", default="constructions,interleaved,flips,cegar")
    ap.add_argument("--flip-keep", type=int, default=10)
    ap.add_argument("--flip-nearest", type=int, default=6)
    ap.add_argument("--cegar-n", type=int, default=25)
    ap.add_argument("--cegar-seconds", type=int, default=300)
    ap.add_argument("--seed", type=int, default=20260905)
    a = ap.parse_args()
    ks = a.k or [6, 7]
    steps = a.steps.split(",")
    cad = cadical_path()
    if not cad:
        print("cadical not found", file=sys.stderr)
        return 3
    failures = []
    errors = []
    summary = {"node": a.node, "steps": {}}
    tmp = Path(a.dataset or ROOT / "harness" / "dataset") / "predecessor_half"
    tmp.mkdir(parents=True, exist_ok=True)
    ce_dir = tmp / "counterexamples"

    if "constructions" in steps:
        checked = []
        for k in ks:
            out = tmp / f"constructions-k{k}.json"
            proc = run_script([SCRIPTS / "baek_balko_constructions.py", "--k", k, "--output", out, "--cadical", cad, "--skip-decomposable"])
            if proc.returncode != 0:
                errors.append({"step": "constructions", "k": k, "rc": proc.returncode})
                continue
            data = json.loads(out.read_text())
            for rec in data["records"]:
                half = rec.get("half_support") or {}
                target = (rec["size"] + 1) // 2
                found = half.get("found", half.get("size", 0) >= target) if isinstance(half, dict) else bool(half)
                checked.append({"k": k, "name": rec["name"], "size": rec["size"], "k_gon_free": rec["k_gon_free"], "half": half})
                if rec["k_gon_free"] and not found:
                    failures.append({"step": "constructions", "k": k, "name": rec["name"], "size": rec["size"], "half_support": half, "points": rec["points"]})
        summary["steps"]["constructions"] = {"checked": len(checked), "records": checked}

    if "interleaved" in steps:
        out = tmp / "interleaved-k7.json"
        proc = run_script([SCRIPTS / "predecessor_half_interleaved_sets.py", "--k", 7, "--random-patterns", 3, "--seed", a.seed,
                           "--pairs", "6,4|4,6;5,5|4,5;5,5|5,4;7,4|4,5;4,7|5,4;7,4|3,6;5,5|3,6;6,4|4,7;6,4|5,4|4,5",
                           "--cadical", cad, "--output", out, "--counterexample-dir", ce_dir])
        if proc.returncode == 2:
            failures.append({"step": "interleaved", "witnesses": sorted(str(p) for p in ce_dir.glob("k7-interleaved-*.json"))})
        elif proc.returncode != 0:
            errors.append({"step": "interleaved", "rc": proc.returncode})
        if out.exists():
            data = json.loads(out.read_text())
            summary["steps"]["interleaved"] = {"tested": data.get("tested"), "counterexamples": data.get("counterexamples"),
                                               "unions": [{key: r.get(key) for key in ("union", "pattern", "size", "pruned", "tested_size", "half")} for r in data["records"]]}

    if "flips" in steps:
        # the nineteen verified heptagon-free 32-point sets of experiment 0108 (Erdős–Szekeres,
        # Theorem 19 and the Valtr blow-ups) when committed; else the constructions step's three
        base = ROOT / "data" / "derived" / "baek-balko-constructions-k7.json"
        if not base.exists():
            base = tmp / "constructions-k7.json"
        if not base.exists():
            proc = run_script([SCRIPTS / "baek_balko_constructions.py", "--k", 7, "--output", base, "--cadical", cad, "--skip-decomposable", "--skip-half"])
        out = tmp / "flips-k7.json"
        proc = run_script([SCRIPTS / "predecessor_half_perturbation_search.py", "--input", base, "--k", 7, "--mode", "flip",
                           "--keep", a.flip_keep, "--nearest", a.flip_nearest, "--seed", a.seed, "--cadical", cad,
                           "--output", out, "--counterexample-dir", ce_dir])
        if proc.returncode != 0:
            errors.append({"step": "flips", "rc": proc.returncode})
        if out.exists():
            data = json.loads(out.read_text())
            per_base = data.get("per_base", [])
            missing = sum(b.get("half_missing", 0) for b in per_base)
            summary["steps"]["flips"] = {"bases": len(per_base), "new_order_types": sum(b.get("new_order_types", 0) for b in per_base),
                                         "half_found": sum(b.get("half_found", 0) for b in per_base), "half_missing": missing}
            if missing:
                failures.append({"step": "flips", "witnesses": sorted(str(p) for p in ce_dir.glob("k7-*flip*.json"))})

    if "cegar" in steps:
        out = tmp / f"cegar-k7-n{a.cegar_n}.json"
        proc = run_script([SCRIPTS / "predecessor_half_k7_cegar.py", "--n", a.cegar_n, "--anchored", "--budget-seconds", a.cegar_seconds,
                           "--cadical", cad, "--output", out, "--counterexample-dir", ce_dir])
        if out.exists():
            data = json.loads(out.read_text())
            summary["steps"]["cegar"] = {"n": data.get("n"), "result": data.get("result"), "iterations": len(data.get("iterations", [])),
                                         "hardest_max_strong_six_free": (data.get("hardest") or {}).get("max_strong_six_free"),
                                         "target": data.get("target"), "seconds": data.get("seconds")}
        if proc.returncode == 2:
            # abstract-tier witness: realizability undetermined, needs a human
            errors.append({"step": "cegar", "rc": 2, "note": "abstract-tier witness; realizability undetermined",
                           "witnesses": sorted(str(p) for p in ce_dir.glob("k7-signotope-*.json"))})
        elif proc.returncode != 0:
            errors.append({"step": "cegar", "rc": proc.returncode})

    summary["failures"] = failures
    summary["errors"] = errors
    print(json.dumps({"steps": list(summary["steps"]), "failures": len(failures), "errors": errors}), file=sys.stderr)
    if a.out:
        Path(a.out).write_text(json.dumps(summary, indent=1))
    if failures:
        return 2
    if errors:
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
