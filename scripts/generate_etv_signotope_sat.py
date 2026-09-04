#!/usr/bin/env python3
"""Erdős–Tuza–Valtr instances at the signotope tier.

For ``N`` ordered vertices, variables are the increasing triples in
lexicographic order (one-based; true = left turn).  Clauses:

* ``one_change``: the rank-three one-change law on every four vertices;
* ``no_cap``: for every ``a``-subset, not every triple is a right turn;
* ``no_cup``: for every ``b``-subset, not every triple is a left turn;
* ``no_gon``: for every ``n``-subset, none of the ``2^(n-2)`` strong
  colorings (each middle vertex on the lower or upper chain);
* ``anchor`` (optional): every triple through vertex 0 is a right turn,
  the normalization proved in ``AnchoredPresentation.lean``.

Satisfiable at ``N`` means a one-change coloring on ``N`` vertices avoids an
``a``-cap, a ``b``-cup, and a strong ``n``-set; the least unsatisfiable ``N``
is the signotope-tier Erdős–Tuza–Valtr number ``N(n, a, b)``, an upper bound
for the planar one.  With ``n`` larger than ``N`` the instance is the
classical cup–cap problem.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import sys
from pathlib import Path


def triples(vertices):
    return list(itertools.combinations(vertices, 3))


def strong_patterns(n: int):
    local = triples(range(n))
    patterns = []
    for assignment in itertools.product((False, True), repeat=n - 2):
        lower = {index + 1 for index in range(n - 2) if assignment[index]}
        patterns.append(tuple(b in lower for a, b, c in local))
    return patterns


def one_change(values) -> bool:
    return sum(x != y for x, y in zip(values, values[1:])) <= 1


def generate(N: int, n: int, a: int, b: int, anchored: bool):
    var = {t: i + 1 for i, t in enumerate(triples(range(N)))}
    records = []
    for quad in itertools.combinations(range(N), 4):
        i, j, m, l = quad
        keys = ((i, j, m), (i, j, l), (i, m, l), (j, m, l))
        for values in itertools.product((False, True), repeat=4):
            if one_change(values):
                continue
            records.append(("one_change", tuple(-var[k] if v else var[k]
                                                for k, v in zip(keys, values))))
    if a <= N:
        for cap in itertools.combinations(range(N), a):
            records.append(("no_cap", tuple(var[t] for t in triples(cap))))
    if b <= N:
        for cup in itertools.combinations(range(N), b):
            records.append(("no_cup", tuple(-var[t] for t in triples(cup))))
    if n <= N:
        patterns = strong_patterns(n)
        for gon in itertools.combinations(range(N), n):
            keys = triples(gon)
            for values in patterns:
                records.append(("no_gon", tuple(-var[k] if v else var[k]
                                                for k, v in zip(keys, values))))
    if anchored:
        for i, j in itertools.combinations(range(1, N), 2):
            records.append(("anchor", (-var[(0, i, j)],)))
    return var, records


def dimacs(variables: int, records) -> str:
    lines = [f"p cnf {variables} {len(records)}"]
    lines.extend(" ".join(map(str, lits)) + " 0" for _, lits in records)
    return "\n".join(lines) + "\n"


def solve(cnf: str, cadical: Path):
    proc = subprocess.run([str(cadical), "-q"], input=cnf, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out = proc.stdout
    if "s UNSATISFIABLE" in out:
        return "UNSAT", None
    if "s SATISFIABLE" in out:
        model = set()
        for line in out.splitlines():
            if line.startswith("v "):
                model.update(int(x) for x in line[2:].split() if int(x) > 0)
        return "SAT", model
    return "UNKNOWN", None


def check_model(var, model, N, a, b, n) -> dict:
    """Independent check of a satisfying coloring against the definitions."""
    color = {t: (v in model) for t, v in var.items()}
    def all_left(vertices):
        return all(color[t] for t in triples(vertices))
    def all_right(vertices):
        return all(not color[t] for t in triples(vertices))
    def strong(vertices):
        # strong: every four-subset i<j<k<l has chi(ijk)=chi(ijl) and chi(ikl)=chi(jkl)
        for i, j, k, l in itertools.combinations(vertices, 4):
            if color[(i, j, k)] != color[(i, j, l)] or color[(i, k, l)] != color[(j, k, l)]:
                return False
        return True
    result = {
        "one_change": all(one_change([color[(i, j, m)], color[(i, j, l)], color[(i, m, l)], color[(j, m, l)]])
                          for i, j, m, l in itertools.combinations(range(N), 4)),
        "cap_free": a > N or not any(all_right(c) for c in itertools.combinations(range(N), a)),
        "cup_free": b > N or not any(all_left(c) for c in itertools.combinations(range(N), b)),
        "gon_free": n > N or not any(strong(g) for g in itertools.combinations(range(N), n)),
    }
    result["valid"] = all(result.values())
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True, help="convex polygon size to avoid")
    parser.add_argument("--a", type=int, required=True, help="cap size to avoid")
    parser.add_argument("--b", type=int, required=True, help="cup size to avoid")
    parser.add_argument("--points", type=int, nargs="+", required=True, help="values of N to decide")
    parser.add_argument("--anchored", action="store_true")
    parser.add_argument("--cadical", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    results = []
    for N in args.points:
        var, records = generate(N, args.n, args.a, args.b, args.anchored)
        cnf = dimacs(len(var), records)
        counts = {}
        for category, _ in records:
            counts[category] = counts.get(category, 0) + 1
        verdict, model = solve(cnf, args.cadical)
        entry = {"N": N, "verdict": verdict, "variables": len(var), "clauses": len(records),
                 "clause_counts": counts, "cnf_sha256": hashlib.sha256(cnf.encode()).hexdigest()}
        if model is not None:
            entry["model_check"] = check_model(var, model, N, args.a, args.b, args.n)
            entry["left_turn_triples"] = sorted(t for t, v in var.items() if v in model)
        print(json.dumps({k: v for k, v in entry.items() if k != "left_turn_triples"}), file=sys.stderr, flush=True)
        results.append(entry)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({
        "generator": "scripts/generate_etv_signotope_sat.py",
        "n": args.n, "a": args.a, "b": args.b, "anchored": args.anchored,
        "results": results}, indent=1) + "\n")


if __name__ == "__main__":
    main()
