#!/usr/bin/env python3
"""Falsifier for the predecessor-half conjecture node (Workstream E).

For each known extremal k-gon-free construction (classical Erdős–Szekeres set and
the Theorem-19 blow-ups from scripts/baek_balko_constructions.py) at the k values
given, check that a (k-1)-gon-free subset of at least half the points exists.
A construction without one is a counterexample to the conjecture's extremal
instance and is written to --out.  Exit 0 = every construction has such a half,
2 = counterexample, other = error.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dataset")
    ap.add_argument("--out")
    ap.add_argument("--node")
    ap.add_argument("--statement")
    ap.add_argument("--k", type=int, action="append", help="k values (default 6 7)")
    a = ap.parse_args()
    ks = a.k or [6, 7]
    cad = cadical_path()
    if not cad:
        print("cadical not found", file=sys.stderr)
        return 3
    failures = []
    checked = []
    tmp = Path(a.dataset or ROOT / "harness" / "dataset") / "predecessor_half"
    tmp.mkdir(parents=True, exist_ok=True)
    for k in ks:
        out = tmp / f"constructions-k{k}.json"
        proc = subprocess.run([sys.executable, str(ROOT / "scripts" / "baek_balko_constructions.py"), "--k", str(k),
                               "--output", str(out), "--cadical", cad, "--skip-decomposable"],
                              capture_output=True, text=True)
        if proc.returncode != 0:
            print(proc.stderr[-2000:], file=sys.stderr)
            return 3
        data = json.loads(out.read_text())
        for rec in data["records"]:
            half = rec.get("half_support") or {}
            target = (rec["size"] + 1) // 2
            found = half.get("found", half.get("size", 0) >= target) if isinstance(half, dict) else bool(half)
            checked.append({"k": k, "name": rec["name"], "size": rec["size"], "k_gon_free": rec["k_gon_free"], "half": half})
            if rec["k_gon_free"] and not found:
                failures.append({"k": k, "name": rec["name"], "size": rec["size"], "half_support": half, "points": rec["points"]})
    print(json.dumps({"checked": len(checked), "failures": len(failures)}), file=sys.stderr)
    if a.out:
        Path(a.out).write_text(json.dumps({"node": a.node, "checked": checked, "failures": failures}, indent=1))
    return 2 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
