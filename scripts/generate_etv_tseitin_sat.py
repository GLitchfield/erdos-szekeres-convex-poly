#!/usr/bin/env python3
"""Erdős–Tuza–Valtr instances at the signotope tier with a hierarchical
Tseitin encoding, for polygon and cup sizes where the direct clause set is
too large (``n = 7`` needs 888,030 seven-sets).

Variables: triple colors (true = left turn), corrected strong-quad atoms,
strong ``m``-set atoms for ``5 ≤ m ≤ n-1``, cup ``m``-set atoms for
``5 ≤ m ≤ b-1``.  Only the direction "all parts strong ⇒ atom" is encoded,
which is sound for refutation (a semantically strong set forces its atom, so
a clause demanding some sub-atom false forbids the strong set) and complete
(atoms may be set to their semantic values).  Clauses: one-change on every
four vertices; no ``a``-cap directly (all triples right forbidden); no
``b``-cup and no strong ``n``-set through the hierarchies; optional anchor.
Satisfying colorings are checked against the definitions directly.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
import sys
import time
from pathlib import Path


def one_change(values) -> bool:
    return sum(x != y for x, y in zip(values, values[1:])) <= 1


class Instance:
    def __init__(self, N, n, a, b, anchored, full=False):
        self.N, self.n, self.a, self.b, self.anchored = N, n, a, b, anchored
        self.full = full
        self.count = 0
        self.clauses = []
        self.counts = {}
        self.triple = {}
        for t in itertools.combinations(range(N), 3):
            self.triple[t] = self.new()

    def new(self):
        self.count += 1
        return self.count

    def add(self, category, lits):
        self.clauses.append(tuple(lits))
        self.counts[category] = self.counts.get(category, 0) + 1

    def build(self):
        N, n, a, b = self.N, self.n, self.a, self.b
        T = self.triple
        for quad in itertools.combinations(range(N), 4):
            i, j, k, l = quad
            keys = ((i, j, k), (i, j, l), (i, k, l), (j, k, l))
            for values in itertools.product((False, True), repeat=4):
                if not one_change(values):
                    self.add("one_change", [-T[key] if v else T[key] for key, v in zip(keys, values)])
        if a <= N:
            for cap in itertools.combinations(range(N), a):
                self.add("no_cap", [T[t] for t in itertools.combinations(cap, 3)])
        # strong-set hierarchy: quad atoms, then m-set atoms up to n-1
        if n <= N:
            quad_atom = {}
            for quad in itertools.combinations(range(N), 4):
                i, j, k, l = quad
                q = self.new(); quad_atom[quad] = q
                t1, t2, t3, t4 = T[(i, j, k)], T[(i, j, l)], T[(i, k, l)], T[(j, k, l)]
                # strong quad: t1 = t2 and t3 = t4; each of the four consistent patterns forces q
                for v12 in (False, True):
                    for v34 in (False, True):
                        lits = [(-t1 if v12 else t1), (-t2 if v12 else t2), (-t3 if v34 else t3), (-t4 if v34 else t4), q]
                        self.add("strong_quad", lits)
                if self.full:
                    # q ⇒ t1 = t2 and q ⇒ t3 = t4
                    self.add("strong_quad_rev", [-q, -t1, t2]); self.add("strong_quad_rev", [-q, t1, -t2])
                    self.add("strong_quad_rev", [-q, -t3, t4]); self.add("strong_quad_rev", [-q, t3, -t4])
            level = quad_atom
            for m in range(5, n):
                nxt = {}
                for X in itertools.combinations(range(N), m):
                    s = self.new(); nxt[X] = s
                    self.add(f"strong_{m}", [-level[Y] for Y in itertools.combinations(X, m - 1)] + [s])
                    if self.full:
                        for Y in itertools.combinations(X, m - 1):
                            self.add(f"strong_{m}_rev", [-s, level[Y]])
                level = nxt
            for X in itertools.combinations(range(N), n):
                self.add("no_gon", [-level[Y] for Y in itertools.combinations(X, n - 1)])
        # cup hierarchy
        if b <= N:
            if b <= 5:
                for cup in itertools.combinations(range(N), b):
                    self.add("no_cup", [-T[t] for t in itertools.combinations(cup, 3)])
            else:
                level = {}
                for X in itertools.combinations(range(N), 5):
                    c = self.new(); level[X] = c
                    self.add("cup_5", [-T[t] for t in itertools.combinations(X, 3)] + [c])
                    if self.full:
                        for t in itertools.combinations(X, 3):
                            self.add("cup_5_rev", [-c, T[t]])
                for m in range(6, b):
                    nxt = {}
                    for X in itertools.combinations(range(N), m):
                        c = self.new(); nxt[X] = c
                        self.add(f"cup_{m}", [-level[Y] for Y in itertools.combinations(X, m - 1)] + [c])
                        if self.full:
                            for Y in itertools.combinations(X, m - 1):
                                self.add(f"cup_{m}_rev", [-c, level[Y]])
                    level = nxt
                for X in itertools.combinations(range(N), b):
                    self.add("no_cup", [-level[Y] for Y in itertools.combinations(X, b - 1)])
        if self.anchored:
            for i, j in itertools.combinations(range(1, N), 2):
                self.add("anchor", [-T[(0, i, j)]])

    def dimacs(self) -> str:
        head = f"p cnf {self.count} {len(self.clauses)}\n"
        return head + "".join(" ".join(map(str, c)) + " 0\n" for c in self.clauses)


def solve(cnf: str, cadical: Path, time_limit: int):
    cmd = [str(cadical), "-q"] + (["-t", str(time_limit)] if time_limit else [])
    started = time.time()
    proc = subprocess.run(cmd, input=cnf, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    seconds = time.time() - started
    out = proc.stdout
    if "s UNSATISFIABLE" in out:
        return "UNSAT", None, seconds
    if "s SATISFIABLE" in out:
        model = set()
        for line in out.splitlines():
            if line.startswith("v "):
                model.update(int(x) for x in line[2:].split() if int(x) > 0)
        return "SAT", model, seconds
    return "UNKNOWN", None, seconds


def check_model(inst: Instance, model) -> dict:
    N, n, a, b = inst.N, inst.n, inst.a, inst.b
    color = {t: (v in model) for t, v in inst.triple.items()}
    def strong(X):
        for i, j, k, l in itertools.combinations(X, 4):
            if color[(i, j, k)] != color[(i, j, l)] or color[(i, k, l)] != color[(j, k, l)]:
                return False
        return True
    res = {
        "one_change": all(one_change([color[(i, j, k)], color[(i, j, l)], color[(i, k, l)], color[(j, k, l)]])
                          for i, j, k, l in itertools.combinations(range(N), 4)),
        "cap_free": a > N or not any(all(not color[t] for t in itertools.combinations(X, 3)) for X in itertools.combinations(range(N), a)),
        "cup_free": b > N or not any(all(color[t] for t in itertools.combinations(X, 3)) for X in itertools.combinations(range(N), b)),
        "gon_free": n > N or not any(strong(X) for X in itertools.combinations(range(N), n)),
    }
    res["valid"] = all(res.values())
    return res


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--b", type=int, required=True)
    parser.add_argument("--points", type=int, nargs="+", required=True)
    parser.add_argument("--anchored", action="store_true")
    parser.add_argument("--full-equivalence", action="store_true", help="also encode atom ⇒ parts")
    parser.add_argument("--time-limit", type=int, default=0, help="seconds per instance (0 = none)")
    parser.add_argument("--cadical", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cnf-dir", type=Path, default=None, help="also write each CNF here")
    args = parser.parse_args()
    results = []
    for N in args.points:
        inst = Instance(N, args.n, args.a, args.b, args.anchored, args.full_equivalence)
        inst.build()
        cnf = inst.dimacs()
        digest = hashlib.sha256(cnf.encode()).hexdigest()
        if args.cnf_dir:
            args.cnf_dir.mkdir(parents=True, exist_ok=True)
            (args.cnf_dir / f"etv-n{args.n}-a{args.a}-b{args.b}-N{N}{'-anchored' if args.anchored else ''}.cnf").write_text(cnf)
        print(json.dumps({"N": N, "variables": inst.count, "clauses": len(inst.clauses), "counts": inst.counts,
                          "cnf_bytes": len(cnf)}), file=sys.stderr, flush=True)
        verdict, model, seconds = solve(cnf, args.cadical, args.time_limit)
        entry = {"N": N, "verdict": verdict, "solver_seconds": round(seconds, 1), "variables": inst.count,
                 "clauses": len(inst.clauses), "clause_counts": inst.counts, "cnf_sha256": digest,
                 "anchored": args.anchored}
        if model is not None:
            entry["model_check"] = check_model(inst, model)
            entry["left_turn_triples"] = sorted(t for t, v in inst.triple.items() if v in model)
        print(json.dumps({k: v for k, v in entry.items() if k != "left_turn_triples"}), file=sys.stderr, flush=True)
        results.append(entry)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({"generator": "scripts/generate_etv_tseitin_sat.py", "n": args.n, "a": args.a,
                                           "b": args.b, "anchored": args.anchored, "full_equivalence": args.full_equivalence, "results": results}, indent=1) + "\n")


if __name__ == "__main__":
    main()
