#!/usr/bin/env python3
"""Label sets for contexts: the injection candidate behind Theorem 8 (note 0123).

Labels are strings over {L, U} of length m = k-2, stored as bitmasks of the L positions.
A single-run context with cup limit cl and cap limit pl at its run gets the cylinder

    L(sigma) = { X : X agrees with the fixed letters on the first f positions,
                 #L(free) <= cl-1, #U(free) <= pl-1 }

with f = max(0, m - (cl-1) - (pl-1)) fixed positions whose letters are the sides of
the f outermost levels of the context (lower -> L, upper -> U; padded with a default
letter when the context has fewer levels).  Its size is the threshold with the run's
internal parameters in both regimes.  A multi-run context gets the union, over all
partitions of its child letters (any interleaving), both orientations and all
couplings, of its parts' label sets, recursively.

The checks, for every context reached from the root (a, u, k) with s child letters:

  DISJOINT: for every partition and coupling, the two parts' label sets are disjoint;
  INSIDE:   for a single-run context, the union over its partitions lies inside the
            rule's own label set;
  SIZE:     the size of a multi-run context's union against the interval-cut
            recursion F2 (information only).

If DISJOINT and INSIDE hold everywhere, every decomposable set satisfying the root
context injects into L(root), whose size is T(a, u, k).
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from functools import lru_cache
from math import comb
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_depth2_tables import limits_from_signature  # noqa: E402
from decomposable_additivity_test import child as child_letters  # noqa: E402
from decomposable_recursive_formula import make_F2, T  # noqa: E402


def run_label_set(word, maxima, a, u, k, default="L", order="outer"):
    """The rule's label set of a single-run context (a frozenset of bitmasks)."""
    m = k - 2
    p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
    assert p == 1
    cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
    if min(cl, pl) < 1:
        return frozenset()
    ell, ups = cl - 1, pl - 1
    f = max(0, m - ell - ups)
    # sides of the levels: level -> side
    side_at = {}
    for w in word:
        if w != "S":
            side_at[w[0]] = w[1]
    nlev = len(maxima)
    levels = list(range(nlev, 0, -1)) if order == "outer" else list(range(1, nlev + 1))
    letters = []
    for i in range(f):
        if i < len(levels) and levels[i] in side_at:
            letters.append("L" if side_at[levels[i]] == "lower" else "U")
        else:
            letters.append(default)
    fixed_mask = (1 << f) - 1
    fixed_L = sum(1 << i for i, c in enumerate(letters) if c == "L")
    free = m - f
    out = set()
    for X in range(1 << m):
        if X & fixed_mask != fixed_L:
            continue
        nL = bin(X >> f).count("1")
        nU = free - nL
        if nL <= ell and nU <= ups:
            out.add(X)
    return frozenset(out)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--s", type=int, default=4, help="child letters at the root")
    ap.add_argument("--default", default="L")
    ap.add_argument("--order", choices=("outer", "inner"), default="outer")
    ap.add_argument("--max-examples", type=int, default=5)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    m = k - 2
    F2 = make_F2(a, u, k)
    stats = {"contexts": 0, "single_run": 0, "multi_run": 0, "partitions": 0,
             "disjoint_violations": 0, "inside_violations": 0, "size_over_F2": 0, "size_under_F2": 0}
    examples = {"disjoint": [], "inside": [], "size_over": [], "size_under": []}

    def fmt(word):
        return "".join("S" if w == "S" else f"{w[0]}{'L' if w[1] == 'lower' else 'U'}" for w in word)

    def lab(X):
        return "".join("L" if X >> i & 1 else "U" for i in range(m))

    @lru_cache(maxsize=None)
    def L(word, maxima):
        stats["contexts"] += 1
        p, _, _ = limits_from_signature(word, maxima, a, u, k)
        s_pos = [i for i, w in enumerate(word) if w == "S"]
        n = len(s_pos)
        union = set()
        if n >= 2:
            for r in range(1, n):
                for keep in itertools.combinations(s_pos, r):
                    A = frozenset(keep)
                    R = frozenset(s_pos) - A
                    for dp in range(1, k - 1):
                        c = k - 1 - dp
                        for (side_a, side_r) in (("lower", "upper"), ("upper", "lower")):
                            wa, ma = child_letters(word, maxima, A, side_a, dp if side_a == "lower" else c)
                            wr, mr = child_letters(word, maxima, R, side_r, c if side_r == "upper" else dp)
                            La = L(wa, ma)
                            Lr = L(wr, mr)
                            stats["partitions"] += 1
                            if La & Lr:
                                stats["disjoint_violations"] += 1
                                if len(examples["disjoint"]) < args.max_examples:
                                    examples["disjoint"].append({"word": fmt(word), "maxima": list(maxima), "A": fmt(wa), "A_max": list(ma), "R": fmt(wr), "R_max": list(mr),
                                                                 "common": [lab(X) for X in sorted(La & Lr)][:6]})
                            union |= La | Lr
        if p == 1:
            stats["single_run"] += 1
            own = run_label_set(word, maxima, a, u, k, args.default, args.order)
            if not union <= own:
                stats["inside_violations"] += 1
                if len(examples["inside"]) < args.max_examples:
                    examples["inside"].append({"word": fmt(word), "maxima": list(maxima), "own": [lab(X) for X in sorted(own)],
                                               "extra": [lab(X) for X in sorted(union - own)][:8]})
            return own
        stats["multi_run"] += 1
        v = F2(word, maxima)
        if len(union) > v:
            stats["size_over_F2"] += 1
            if len(examples["size_over"]) < args.max_examples:
                examples["size_over"].append({"word": fmt(word), "maxima": list(maxima), "union": len(union), "F2": v})
        elif len(union) < v:
            stats["size_under_F2"] += 1
            if len(examples["size_under"]) < args.max_examples:
                examples["size_under"].append({"word": fmt(word), "maxima": list(maxima), "union": len(union), "F2": v})
        return frozenset(union)

    started = time.time()
    root = (tuple(["S"] * args.s), tuple())
    Lroot = L(*root)
    result = {"case": args.case, "s": args.s, "default": args.default, "order": args.order,
              "root_size": len(Lroot), "threshold": T(a, u, k), "seconds": round(time.time() - started, 1),
              "stats": stats, "examples": examples}
    print(json.dumps({k_: v for k_, v in result.items() if k_ != "examples"}))
    for key, exs in examples.items():
        for e in exs:
            print(f"{key}: {json.dumps(e)}")
    if args.output:
        args.output.write_text(json.dumps(result, indent=1) + "\n")


if __name__ == "__main__":
    main()
