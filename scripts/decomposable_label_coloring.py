#!/usr/bin/env python3
"""Existence of label sets for contexts, as a coloring problem (note 0123).

Contexts reachable from the root (a, u, k) with s child letters by repeated partitions
of the child letters (any interleaving, both orientations, all couplings) form a DAG;
its leaves are the one-vertex contexts with positive limits.  A system of label sets
L(sigma) with L(part_A) and L(part_R) disjoint inside L(sigma) at every split, nonempty
at every leaf and of size at most C at the root exists iff the leaves can be colored
with C colors such that no split has both parts reaching leaves of the same color
(reachability through any chain of splits).  With C = T(a, u, k) this is exactly the
injection that would prove Theorem 8 at the level of contexts.

Encoding: y[c, x] (leaf c has color x), z[sigma, x] (some leaf below sigma has color x);
z[leaf, x] <- y[leaf, x]; z[sigma, x] <- z[part, x] for every part of sigma;
at every split: not (z[part_A, x] and z[part_R, x]); every leaf has a color.
SAT gives a coloring (and the label sets); UNSAT refutes the context-level conjecture
for these parameters.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_depth2_tables import limits_from_signature  # noqa: E402
from decomposable_additivity_test import child as child_letters  # noqa: E402
from decomposable_recursive_formula import T  # noqa: E402


def build(a, u, k, s, prune_dead):
    root = (tuple(["S"] * s), tuple())
    index = {root: 0}
    contexts = [root]
    splits = []          # (parent, partA, partR)
    leaves = set()
    dead = set()
    stack = [root]
    while stack:
        ctx = stack.pop()
        word, maxima = ctx
        i = index[ctx]
        s_pos = [p for p, w in enumerate(word) if w == "S"]
        n = len(s_pos)
        if n == 1:
            p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
            if min(int(cup_limit[0][0]), int(cap_limit[0][0])) >= 1:
                leaves.add(i)
            else:
                dead.add(i)
            continue
        if prune_dead:
            p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
            if min(int(cup_limit[0][0]), int(cap_limit[0][0])) < 1:
                dead.add(i)
                continue
        for r in range(1, n):
            for keep in itertools.combinations(s_pos, r):
                A = frozenset(keep)
                R = frozenset(s_pos) - A
                for dp in range(1, k - 1):
                    c = k - 1 - dp
                    for side_a, side_r in (("lower", "upper"), ("upper", "lower")):
                        pa = child_letters(word, maxima, A, side_a, dp if side_a == "lower" else c)
                        pr = child_letters(word, maxima, R, side_r, c if side_r == "upper" else dp)
                        ids = []
                        for part in (pa, pr):
                            if part not in index:
                                index[part] = len(contexts)
                                contexts.append(part)
                                stack.append(part)
                            ids.append(index[part])
                        splits.append((i, ids[0], ids[1]))
    return contexts, splits, leaves, dead


CADICAL = Path.home() / ".elan/toolchains/leanprover--lean4---v4.29.1/bin/cadical"


def solve(contexts, splits, leaves, colors, solver_name, cnf_path=None):
    ncx = len(contexts)
    def y(c, x): return 1 + c * colors + x
    def z(i, x): return 1 + ncx * colors + i * colors + x
    clauses = []
    for c in leaves:
        clauses.append([y(c, x) for x in range(colors)])
        for x in range(colors):
            clauses.append([-y(c, x), z(c, x)])
    for (i, ia, ir) in splits:
        for x in range(colors):
            clauses.append([-z(ia, x), z(i, x)])
            clauses.append([-z(ir, x), z(i, x)])
            clauses.append([-z(ia, x), -z(ir, x)])
    nvars = 2 * ncx * colors
    model = None
    try:
        from pysat.solvers import Solver
        with Solver(name=solver_name, bootstrap_with=clauses) as sol:
            ok = sol.solve()
            model = sol.get_model() if ok else None
    except ImportError:
        import subprocess, tempfile
        path = cnf_path or Path(tempfile.mkdtemp()) / "coloring.cnf"
        with open(path, "w") as f:
            f.write(f"p cnf {nvars} {len(clauses)}\n")
            for cl in clauses:
                f.write(" ".join(map(str, cl)) + " 0\n")
        proc = subprocess.run([str(CADICAL), "-q", str(path)], capture_output=True, text=True)
        ok = proc.returncode == 10
        if ok:
            model = []
            for line in proc.stdout.splitlines():
                if line.startswith("v "):
                    model.extend(int(t) for t in line[2:].split() if t != "0")
        elif proc.returncode != 20:
            raise RuntimeError(f"cadical rc={proc.returncode}: {proc.stderr[-500:]}")
    coloring = None
    if ok:
        pos = set(v for v in model if v > 0)
        coloring = {c: [x for x in range(colors) if y(c, x) in pos][0] for c in leaves}
    return ok, coloring, len(clauses)


def fmt(word):
    return "".join("S" if w == "S" else f"{w[0]}{'L' if w[1] == 'lower' else 'U'}" for w in word)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--s", type=int, default=4)
    ap.add_argument("--colors", type=int, default=None, help="default T(a,u,k)")
    ap.add_argument("--no-prune", action="store_true", help="keep contexts with a zero limit")
    ap.add_argument("--solver", default="cadical153")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    colors = args.colors or T(a, u, k)
    started = time.time()
    contexts, splits, leaves, dead = build(a, u, k, args.s, not args.no_prune)
    built = time.time() - started
    ok, coloring, nclauses = solve(contexts, splits, leaves, colors, args.solver)
    result = {"case": args.case, "s": args.s, "colors": colors, "threshold": T(a, u, k),
              "contexts": len(contexts), "splits": len(splits), "leaves": len(leaves), "dead": len(dead),
              "clauses": nclauses, "sat": ok, "build_seconds": round(built, 1), "seconds": round(time.time() - started, 1)}
    print(json.dumps(result), flush=True)
    if args.output:
        out = dict(result)
        if coloring:
            out["coloring"] = {fmt(contexts[c][0]) + "|" + ",".join(map(str, contexts[c][1])): x for c, x in coloring.items()}
        args.output.write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
