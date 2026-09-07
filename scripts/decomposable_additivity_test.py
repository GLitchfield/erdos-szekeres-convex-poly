#!/usr/bin/env python3
"""Workstream B, step 3: is the recursion F (experiment 0120) additive across
arbitrary splits of abstract contexts?

F(context) is defined through cuts at run boundaries (stacked).  The inductive
step of a proof of Theorem 8 needs, for every context sigma, every partition of
its vertices into a lower part L and an upper part U (any interleaving, cuts
inside runs included) and every coupling d' (the lower part sees a sibling of longest cap d', the upper part a
sibling of longest cup k-1-d'):

    F(sigma_L) + F(sigma_U) <= F(sigma)

where sigma_L is L's own context with U added as a level-1 sibling (and the
mirror orientation with L upper).  This script enumerates abstract contexts
(words over S and tagged external vertices at levels 1..--levels with all
sibling maxima), every partition of the S-letters that is not itself a
run-boundary cut, and both orientations, and reports every violation.  A clean
run on small contexts is the tested form of the additivity statement; a
violation is a context the paper argument must handle differently.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_recursive_formula import make_F, run_index  # noqa: E402


def contexts(s_max, e_max, levels, k, *, include_unused_levels=False):
    """Yield (word, maxima) with s S-letters and e external letters."""
    for s in range(2, s_max + 1):
        for e in range(0, e_max + 1):
            n = s + e
            for ext_positions in itertools.combinations(range(n), e):
                for tags in itertools.product([(l, side) for l in range(1, levels + 1) for side in ("lower", "upper")], repeat=e):
                    present = sorted({t[0] for t in tags})
                    if not include_unused_levels and present != list(range(1, len(present) + 1)):
                        continue                      # levels must be 1..L consecutively
                    # one side per level (a level is one split)
                    side_at = {}
                    ok = True
                    for l, side in tags:
                        if side_at.setdefault(l, side) != side:
                            ok = False
                    if not ok:
                        continue
                    word = ["S"] * n
                    for pos, t in zip(ext_positions, tags):
                        word[pos] = t
                    depths = range(max(present, default=0), levels + 1) if include_unused_levels else [len(present)]
                    for depth in depths:
                        for maxima in itertools.product(range(1, k - 1), repeat=depth):
                            yield tuple(word), tuple(maxima)


def child(word, maxima, keep, side_of_child, sibling_max):
    new_word = []
    for i, w in enumerate(word):
        if w == "S":
            new_word.append("S" if i in keep else (1, side_of_child))
        else:
            new_word.append((w[0] + 1, w[1]))
    return tuple(new_word), (sibling_max,) + tuple(maxima)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--s-max", type=int, default=5)
    parser.add_argument("--e-max", type=int, default=2)
    parser.add_argument("--levels", type=int, default=2)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--recursion", choices=("F", "F2", "lean"), default="F",
                        help="F: run-boundary cuts; F2: interval cuts with positive children; "
                             "lean: literal Lean interval recurrence, including zero children and unused levels")
    parser.add_argument("--shard", default=None, help="i/N: test only every N-th context starting at i (independent shards, merge with --merge)")
    parser.add_argument("--cache-size", type=int, default=None, help="bound the recursion's memoization table (entries)")
    args = parser.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    shard_i, shard_n = (int(x) for x in args.shard.split("/")) if args.shard else (0, 1)
    if args.cache_size:
        import decomposable_recursive_formula as drf
        drf.CACHE_SIZE = args.cache_size
    include_zero_children = args.recursion == "lean"
    if args.recursion in ("F2", "lean"):
        from decomposable_recursive_formula import make_F2
        F = make_F2(a, u, k, include_zero_children=include_zero_children)
    else:
        F = make_F(a, u, k)
    started = time.time()
    stats = {"contexts": 0, "nonzero_contexts": 0, "partitions": 0, "violations": 0, "slack_histogram": {}}
    violations = []
    for index, (word, maxima) in enumerate(contexts(
            args.s_max, args.e_max, args.levels, k, include_unused_levels=include_zero_children)):
        if index % shard_n != shard_i:
            continue
        stats["contexts"] += 1
        value = F(word, maxima)
        if value == 0 and not include_zero_children:
            continue
        stats["nonzero_contexts"] += int(value != 0)
        s_pos = [i for i, w in enumerate(word) if w == "S"]
        runs = run_index(word)
        for r in range(1, 1 << len(s_pos)):
            if r == (1 << len(s_pos)) - 1:
                continue
            L = frozenset(s_pos[i] for i in range(len(s_pos)) if r >> i & 1)
            U = frozenset(s_pos) - L
            # skip run-boundary cuts (they are F's own cuts)
            lr = {runs[i] for i in L}; ur = {runs[i] for i in U}
            if not include_zero_children and not (lr & ur) and (max(lr) < min(ur) or max(ur) < min(lr)):
                continue
            stats["partitions"] += 1
            best = 0
            best_witness = None
            for dp in range(1, k - 1):
                c = k - 1 - dp
                # orientation 1: L lower (sees U's longest cap d'), U upper (sees L's longest cup c)
                w1, m1 = child(word, maxima, L, "lower", dp); w2, m2 = child(word, maxima, U, "upper", c)
                v1 = F(w1, m1); v2 = F(w2, m2) if include_zero_children or v1 else 0
                if (include_zero_children or (v1 and v2)) and v1 + v2 > best:
                    best = v1 + v2
                    best_witness = {"d": dp, "side": "lower", "part_bounds": [v1, v2]}
                # orientation 2: L upper, U lower
                w1, m1 = child(word, maxima, L, "upper", c); w2, m2 = child(word, maxima, U, "lower", dp)
                v1 = F(w1, m1); v2 = F(w2, m2) if include_zero_children or v1 else 0
                if (include_zero_children or (v1 and v2)) and v1 + v2 > best:
                    best = v1 + v2
                    best_witness = {"d": dp, "side": "upper", "part_bounds": [v1, v2]}
            slack = value - best
            stats["slack_histogram"][slack] = stats["slack_histogram"].get(slack, 0) + 1
            if best > value:
                stats["violations"] += 1
                if len(violations) < 30:
                    violations.append({"word": ["S" if w == "S" else f"{w[0]}{'L' if w[1]=='lower' else 'U'}" for w in word],
                                       "maxima": list(maxima), "F": value, "L": sorted(L), "U": sorted(U),
                                       "best_split": best, "witness": best_witness})
    stats["slack_histogram"] = dict(sorted(stats["slack_histogram"].items()))
    stats["seconds"] = round(time.time() - started, 1)
    out = {"case": args.case, "recursion": args.recursion,
           "domain": "well_formed" if include_zero_children else "occupied_levels",
           "shard": args.shard, "s_max": args.s_max, "e_max": args.e_max,
           "levels": args.levels, "stats": stats, "violations": violations}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps({"case": args.case, **stats}), file=sys.stderr)


if __name__ == "__main__":
    main()
