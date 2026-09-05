#!/usr/bin/env python3
"""Workstream E falsifier, third form: the signotope-tier instance at k = 7.

Searches for a one-change coloring on n vertices with no strong 7-set in which
every ceil(n/2)-subset contains a strong 6-set: an abstract-tier counterexample
to `PredecessorHalfSubsetAt 7` (a realizable one would refute the
predecessor-half conjecture; realizability is checked separately, this script
only finds candidates).  The "every half has a strong six" constraint has
C(n, n/2) clauses and is not written down; it is learned counterexample-guided:

  main instance: one-change law on every four vertices; Tseitin atoms for
    strong quads, strong 5-sets and strong 6-sets (both implication directions,
    so the atoms are exact); no strong 7-set (for every 7-subset, one of its
    six-subsets is not strong); optional anchoring of vertex 0 (sound for
    strong-set constraints, AnchoredPresentation.lean; unsound for caps/cups).
  loop: solve -> coloring chi -> strong 6-sets of chi (read off the atoms and
    re-verified) -> half search: a ceil(n/2)-subset meeting no strong 6-set,
    by SAT with a sequential-counter cardinality constraint -> UNSAT means chi
    is an abstract counterexample (written to --counterexample-dir; stop);
    otherwise, for up to --halves-per-iteration distinct halves S, add the
    clause "S contains a strong 6-set" (OR of the strong-6 atoms of S) to the
    main instance and solve again.

Backends: `pysat` (incremental CaDiCaL through python-sat, preferred) or the
`cadical` binary (re-solves the growing instance from a file each iteration).
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import tempfile
import time
from pathlib import Path


# ------------------------------------------------------------ solvers

class CadicalFile:
    """Non-incremental backend: keep every clause, re-solve from a DIMACS file."""

    def __init__(self, path: Path, variables: int):
        self.path = path
        self.clauses: list[list[int]] = []
        self.variables = variables

    def add_clause(self, clause):
        self.clauses.append(list(clause))

    def solve(self):
        with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as handle:
            handle.write(f"p cnf {self.variables} {len(self.clauses)}\n")
            for clause in self.clauses:
                handle.write(" ".join(map(str, clause)) + " 0\n")
            name = handle.name
        try:
            proc = subprocess.run([str(self.path), "-q", name], text=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        finally:
            os.unlink(name)
        out = proc.stdout
        if "s UNSATISFIABLE" in out:
            return False, None
        if "s SATISFIABLE" not in out:
            raise RuntimeError(out[:300])
        model = set()
        for line in out.splitlines():
            if line.startswith("v "):
                model.update(int(x) for x in line[2:].split() if int(x) > 0)
        return True, model


class PysatSolver:
    def __init__(self, variables: int):
        from pysat.solvers import Cadical195
        self.solver = Cadical195()
        self.variables = variables
        self.count = 0

    def add_clause(self, clause):
        self.solver.add_clause(list(clause))
        self.count += 1

    def solve(self):
        if not self.solver.solve():
            return False, None
        return True, {v for v in self.solver.get_model() if v > 0}


def resolve_backend(backend: str) -> str:
    if backend != "auto":
        return backend
    try:
        import pysat.solvers  # noqa: F401
        return "pysat"
    except ImportError:
        return "cadical"


def make_solver(backend: str, cadical: Path | None, variables: int):
    backend = resolve_backend(backend)
    if backend == "pysat":
        return PysatSolver(variables)
    if cadical is None:
        raise SystemExit("--cadical is required for the cadical backend")
    return CadicalFile(cadical, variables)


# ----------------------------------------------------------- encoding

def build(n: int, anchored: bool, backend: str, cadical: Path | None):
    tri = {}
    for t in itertools.combinations(range(n), 3):
        tri[t] = len(tri) + 1
    offset = len(tri)
    quad = {}
    for q in itertools.combinations(range(n), 4):
        quad[q] = offset + len(quad) + 1
    offset += len(quad)
    five = {}
    for s in itertools.combinations(range(n), 5):
        five[s] = offset + len(five) + 1
    offset += len(five)
    six = {}
    for s in itertools.combinations(range(n), 6):
        six[s] = offset + len(six) + 1
    offset += len(six)
    solver = make_solver(backend, cadical, offset)
    counts = {}

    def add(kind, clause):
        solver.add_clause(clause)
        counts[kind] = counts.get(kind, 0) + 1

    for (i, j, k, l), q in quad.items():
        t1, t2, t3, t4 = tri[(i, j, k)], tri[(i, j, l)], tri[(i, k, l)], tri[(j, k, l)]
        keys = (t1, t2, t3, t4)
        for values in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(values, values[1:])) > 1:
                add("one_change", [-v if val else v for v, val in zip(keys, values)])
        # q -> (t1 = t2) and (t3 = t4)
        add("quad_to", [-q, t1, -t2]); add("quad_to", [-q, -t1, t2])
        add("quad_to", [-q, t3, -t4]); add("quad_to", [-q, -t3, t4])
        # (t1 = t2) and (t3 = t4) -> q
        for a in (False, True):
            for b in (False, True):
                add("quad_from", [q, -t1 if a else t1, -t2 if a else t2, -t3 if b else t3, -t4 if b else t4])
    for s, v in five.items():
        qs = [quad[c] for c in itertools.combinations(s, 4)]
        add("five_from", [v] + [-x for x in qs])
        for x in qs:
            add("five_to", [-v, x])
    for s, v in six.items():
        fs = [five[c] for c in itertools.combinations(s, 5)]
        add("six_from", [v] + [-x for x in fs])
        for x in fs:
            add("six_to", [-v, x])
    for u in itertools.combinations(range(n), 7):
        add("no_strong_seven", [-six[c] for c in itertools.combinations(u, 6)])
    if anchored:
        for i, j in itertools.combinations(range(1, n), 2):
            add("anchor", [-tri[(0, i, j)]])
    return solver, tri, quad, five, six, counts, offset


def coloring_of(model, tri):
    return {t: (v in model) for t, v in tri.items()}


def strong_six_sets(color, n, model, six):
    """Strong 6-sets of the coloring, read off the atoms and re-verified."""
    def strong(vertices):
        for i, j, k, l in itertools.combinations(vertices, 4):
            if color[(i, j, k)] != color[(i, j, l)] or color[(i, k, l)] != color[(j, k, l)]:
                return False
        return True
    from_atoms = [s for s, v in six.items() if v in model]
    for s in from_atoms:
        if not strong(s):
            raise RuntimeError(f"atom {s} true but the 6-set is not strong")
    return from_atoms, strong


def sinz_at_least(n, target, next_var):
    """Clauses forcing at least ``target`` of x_1..x_n true (sequential counter
    on the negations), starting auxiliary variables at ``next_var``."""
    clauses = []
    bound = n - target
    lits = [-(i + 1) for i in range(n)]
    if bound == 0:
        return [[-l] for l in lits], next_var
    s = [[0] * (bound + 1) for _ in range(n)]
    for i in range(n):
        for j in range(1, bound + 1):
            s[i][j] = next_var
            next_var += 1
    clauses.append([-lits[0], s[0][1]])
    for j in range(2, bound + 1):
        clauses.append([-s[0][j]])
    for i in range(1, n):
        clauses.append([-lits[i], s[i][1]])
        clauses.append([-s[i - 1][1], s[i][1]])
        for j in range(2, bound + 1):
            clauses.append([-lits[i], -s[i - 1][j - 1], s[i][j]])
            clauses.append([-s[i - 1][j], s[i][j]])
        clauses.append([-lits[i], -s[i - 1][bound]])
    return clauses, next_var


def free_subsets(n, strong6, target, limit, backend, cadical):
    """Up to ``limit`` distinct ``target``-subsets meeting no strong 6-set."""
    card, next_var = sinz_at_least(n, target, n + 1)
    solver = make_solver(backend, cadical, next_var - 1)
    for s in strong6:
        solver.add_clause([-(v + 1) for v in s])
    for c in card:
        solver.add_clause(c)
    found = []
    while len(found) < limit:
        sat, model = solver.solve()
        if not sat:
            break
        chosen = sorted(v - 1 for v in model if 0 < v <= n)
        chosen = chosen[:target]  # any target-subset of a strong-6-free set is strong-6-free; the clause is stronger
        found.append(chosen)
        solver.add_clause([-(v + 1) for v in chosen])
    return found


def max_free_size(n, strong6, lower, backend, cadical):
    size = lower
    while size < n:
        if not free_subsets(n, strong6, size + 1, 1, backend, cadical):
            break
        size += 1
    return size


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--k", type=int, default=7, help="only 7 is implemented (strong-6 atoms)")
    parser.add_argument("--anchored", action="store_true")
    parser.add_argument("--backend", choices=("auto", "pysat", "cadical"), default="auto")
    parser.add_argument("--cadical", type=Path, default=None)
    parser.add_argument("--halves-per-iteration", type=int, default=8)
    parser.add_argument("--budget-seconds", type=float, default=1800)
    parser.add_argument("--max-iterations", type=int, default=10 ** 9)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--counterexample-dir", type=Path, required=True)
    args = parser.parse_args()
    if args.k != 7:
        raise SystemExit("only k = 7 is implemented")
    n = args.n
    target = (n + 1) // 2
    started = time.time()
    solver, tri, quad, five, six, counts, variables = build(n, args.anchored, args.backend, args.cadical)
    build_seconds = round(time.time() - started, 1)
    print(json.dumps({"n": n, "anchored": args.anchored, "variables": variables, "clauses": counts,
                      "build_seconds": build_seconds}), file=sys.stderr, flush=True)
    iterations = []
    hardest = None
    result = "budget"
    iteration = 0
    while iteration < args.max_iterations and time.time() - started < args.budget_seconds:
        iteration += 1
        t0 = time.time()
        sat, model = solver.solve()
        solve_seconds = round(time.time() - t0, 1)
        if not sat:
            result = "unsat"
            print(json.dumps({"iteration": iteration, "verdict": "UNSAT", "note": "no anchored one-change coloring survives the learned halves" if args.anchored else "abstract-tier theorem at this n"}), file=sys.stderr, flush=True)
            break
        color = coloring_of(model, tri)
        strong6, strong = strong_six_sets(color, n, model, six)
        halves = free_subsets(n, strong6, target, args.halves_per_iteration, args.backend, args.cadical)
        entry = {"iteration": iteration, "solve_seconds": solve_seconds, "strong_six_sets": len(strong6),
                 "halves_found": len(halves), "elapsed": round(time.time() - started, 1)}
        if not halves:
            result = "counterexample"
            args.counterexample_dir.mkdir(parents=True, exist_ok=True)
            path = args.counterexample_dir / f"k7-signotope-n{n}{'-anchored' if args.anchored else ''}.json"
            path.write_text(json.dumps({"n": n, "anchored": args.anchored, "target": target,
                                        "left_turn_triples": sorted(t for t, v in color.items() if v),
                                        "strong_six_sets": len(strong6), "iteration": iteration,
                                        "realizability": "undetermined"}, indent=1))
            entry["counterexample"] = str(path)
            print(f"ALERT: abstract-tier counterexample at n={n}: {path} (realizability undetermined)", file=sys.stderr, flush=True)
            iterations.append(entry)
            break
        max_free = max_free_size(n, strong6, target, args.backend, args.cadical)
        entry["max_strong_six_free"] = max_free
        if hardest is None or max_free < hardest["max_strong_six_free"]:
            hardest = {"iteration": iteration, "max_strong_six_free": max_free,
                       "left_turn_triples": sorted(t for t, v in color.items() if v)}
        for half in halves:
            solver.add_clause([six[c] for c in itertools.combinations(tuple(half), 6)])
        entry["learned_clauses_total"] = sum(len(h) and 1 for h in halves) + (iterations[-1]["learned_clauses_total"] if iterations else 0)
        iterations.append(entry)
        print(json.dumps(entry), file=sys.stderr, flush=True)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({"n": n, "anchored": args.anchored, "target": target, "backend": args.backend,
                                           "variables": variables, "clauses": counts, "result": "running",
                                           "iterations": iterations, "hardest": hardest}, indent=1) + "\n")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"n": n, "anchored": args.anchored, "target": target, "backend": args.backend,
                                       "variables": variables, "clauses": counts, "result": result,
                                       "seconds": round(time.time() - started, 1),
                                       "iterations": iterations, "hardest": hardest}, indent=1) + "\n")
    print(json.dumps({"n": n, "result": result, "iterations": len(iterations), "seconds": round(time.time() - started, 1)}), file=sys.stderr)
    return 2 if result == "counterexample" else 0


if __name__ == "__main__":
    sys.exit(main())
