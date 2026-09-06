#!/usr/bin/env python3
"""Label sets as a function of context features, by SAT (note 0123).

Variables w[phi, x]: label x (a string over {L,U} of length k-2) belongs to the label set
of every context with feature vector phi.  Constraints, over all contexts reachable from
the root (a, u, k) with s child letters by any partition, orientation and coupling:

  leaf (one child letter, positive limits): its label set is nonempty;
  split sigma -> (A, R): L(A) and L(R) are disjoint and both inside L(sigma);
  root: at most T(a, u, k) labels (or the given --colors).

--features chooses phi:
  context : the whole (word, maxima)            (the bare label-set conjecture)
  limits  : (number of child letters, cl, pl)   the run limits of single-run contexts,
            and the whole context otherwise
  sides   : limits plus the sides of the levels (innermost first)
  maxima  : sides plus the sibling maxima
  word    : limits plus the whole word (positions and sides), but not the maxima
SAT exhibits a rule; UNSAT says the labels must depend on more than phi.
"""
from __future__ import annotations

import argparse
import itertools
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_depth2_tables import limits_from_signature  # noqa: E402
from decomposable_label_coloring import build, CADICAL, fmt  # noqa: E402
from decomposable_recursive_formula import T  # noqa: E402


def features(ctx, a, u, k, mode):
    word, maxima = ctx
    if mode == "context":
        return ctx
    p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
    n = sum(1 for w in word if w == "S")
    if p != 1:
        return ("multi",) + ctx
    cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
    base = (n, cl, pl)
    if mode == "limits":
        return base
    if mode == "word":
        return base + (word,)
    side_at = {}
    for w in word:
        if w != "S":
            side_at[w[0]] = w[1]
    sides = tuple(side_at.get(l, "-") for l in range(1, len(maxima) + 1))
    if mode == "sides":
        return base + (sides,)
    return base + (sides, tuple(maxima))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--s", type=int, default=4)
    ap.add_argument("--colors", type=int, default=None)
    ap.add_argument("--features", choices=("context", "limits", "sides", "maxima", "word"), default="context")
    ap.add_argument("--root-window", action="store_true",
                    help="pin the root's label set to the canonical window (fixed trailing U's in the choose regime)")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    m = k - 2
    nlab = 1 << m
    colors = args.colors or T(a, u, k)
    started = time.time()
    contexts, splits, leaves, dead = build(a, u, k, args.s, True)
    phi_index = {}
    phi_of = []
    for ctx in contexts:
        phi = features(ctx, a, u, k, args.features)
        if phi not in phi_index:
            phi_index[phi] = len(phi_index)
        phi_of.append(phi_index[phi])
    nphi = len(phi_index)
    def w(f, x): return 1 + f * nlab + x
    clauses = []
    for c in leaves:
        clauses.append([w(phi_of[c], x) for x in range(nlab)])
    seen = set()
    for (i, ia, ir) in splits:
        key = (phi_of[i], phi_of[ia], phi_of[ir])
        if key in seen:
            continue
        seen.add(key)
        fi, fa, fr = key
        for x in range(nlab):
            clauses.append([-w(fa, x), w(fi, x)])
            clauses.append([-w(fr, x), w(fi, x)])
            clauses.append([-w(fa, x), -w(fr, x)])
    # root cardinality: at most `colors` labels
    froot = phi_of[0]
    if args.root_window:
        free = min(m, a + u - 4)
        fixed = m - free
        for x in range(nlab):
            nL = bin(x & ((1 << free) - 1)).count("1")
            nU = free - nL
            trailing_ok = (x >> free) == 0          # fixed positions carry U
            inside = trailing_ok and nL <= u - 2 and nU <= a - 2
            clauses.append([w(froot, x)] if inside else [-w(froot, x)])
    elif colors < nlab:
        for sub in itertools.combinations(range(nlab), colors + 1):
            clauses.append([-w(froot, x) for x in sub])
    nvars = nphi * nlab
    path = Path(tempfile.mkdtemp()) / "rule.cnf"
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
    proc = subprocess.run([str(CADICAL), "-q", str(path)], capture_output=True, text=True)
    sat = proc.returncode == 10
    if proc.returncode not in (10, 20):
        raise RuntimeError(proc.stderr[-500:])
    result = {"case": args.case, "s": args.s, "features": args.features, "colors": colors, "threshold": T(a, u, k),
              "contexts": len(contexts), "feature_classes": nphi, "leaves": len(leaves), "clauses": len(clauses),
              "sat": sat, "seconds": round(time.time() - started, 1)}
    print(json.dumps(result), flush=True)
    if args.output and not sat:
        args.output.write_text(json.dumps(result, indent=1) + "\n")
    if sat and args.output:
        pos = set()
        for line in proc.stdout.splitlines():
            if line.startswith("v "):
                pos.update(int(t) for t in line[2:].split() if t != "0" and int(t) > 0)
        def lab(x): return "".join("L" if x >> i & 1 else "U" for i in range(m))
        sets = {}
        for phi, f in phi_index.items():
            labels = [lab(x) for x in range(nlab) if w(f, x) in pos]
            key = fmt(phi[0]) + "|" + ",".join(map(str, phi[1])) if args.features == "context" else json.dumps(phi, default=str)
            sets[key] = labels
        result["label_sets"] = sets
        args.output.write_text(json.dumps(result, indent=1, default=str) + "\n")


if __name__ == "__main__":
    main()
