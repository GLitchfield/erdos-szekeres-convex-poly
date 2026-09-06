#!/usr/bin/env python3
"""Test the path lemma behind Theorem 8's formula.

T(a,u,k) counts binary strings of length k-2 with at most u-2 letters L and at most
a-2 letters U (window regime; the choose and diagonal regimes agree).  A decomposable
coloring is a binary tree whose leaves are the vertices, so |S| <= T would follow at
once from: in some (or every) decomposition tree of a coloring with no u-cup, no
a-cap and no strong k-set, every root-to-leaf path has at most u-2 lower-steps,
at most a-2 upper-steps and length at most k-2 (leaf paths are prefix-free).

For every decomposable coloring on n <= --max-n vertices this script computes
cupmax, capmax, strongmax and, over all decomposition trees, per leaf the number of
lower-steps L, upper-steps U and the depth D, and tests

  ALL:    every tree, every leaf:  L <= cupmax-1, U <= capmax-1, D <= strongmax-1
  EXISTS: some tree satisfies it for every leaf
  SWAP:   the same with the roles of L and U exchanged (which side extends what)

and records the violations.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import enumerate_class, coloring_dict  # noqa: E402
from decomposable_context_functions import classify_subsets, deep_below_split_ok, restrict_mask  # noqa: E402


def maxima(chi, n):
    cup, cap, strong = classify_subsets(chi, n)
    def mx(d):
        return max(bin(m).count("1") for m, ok in d.items() if ok)
    return mx(cup), mx(cap), mx(strong)


def splits(chi, vs, class_masks, tindex):
    out = []
    for lower_bits in range(1, (1 << len(vs)) - 1):
        lower = tuple(v for i, v in enumerate(vs) if lower_bits >> i & 1)
        upper = tuple(v for i, v in enumerate(vs) if not lower_bits >> i & 1)
        if not deep_below_split_ok(chi, vs, set(lower)):
            continue
        if not restrict_mask(chi, lower, class_masks, tindex)[1]:
            continue
        if not restrict_mask(chi, upper, class_masks, tindex)[1]:
            continue
        out.append((lower, upper))
    return out


def analyze(chi, n, class_masks, tindex):
    """Return (all_ok, exists_ok, worst) for the direct assignment and the swapped one."""
    cupmax, capmax, strongmax = maxima(chi, n)
    memo_splits = {}

    def get_splits(vs):
        if vs not in memo_splits:
            memo_splits[vs] = splits(chi, vs, class_masks, tindex)
        return memo_splits[vs]

    # ALL: enumerate every path (node, L, U, D) reachable
    worst = {"L": 0, "U": 0, "D": 0}
    stack = [(tuple(range(n)), 0, 0, 0)]
    seen = set()
    while stack:
        vs, L, U, D = stack.pop()
        if (vs, L, U, D) in seen:
            continue
        seen.add((vs, L, U, D))
        if len(vs) == 1:
            worst["L"] = max(worst["L"], L)
            worst["U"] = max(worst["U"], U)
            worst["D"] = max(worst["D"], D)
            continue
        for lower, upper in get_splits(vs):
            stack.append((lower, L + 1, U, D + 1))
            stack.append((upper, L, U + 1, D + 1))
    all_ok = worst["L"] <= cupmax - 1 and worst["U"] <= capmax - 1 and worst["D"] <= strongmax - 1
    all_ok_swap = worst["U"] <= cupmax - 1 and worst["L"] <= capmax - 1 and worst["D"] <= strongmax - 1

    # EXISTS: a tree where every leaf satisfies the bounds (DP over node with counts)
    memo = {}

    def good(vs, L, U, D, lim_L, lim_U, lim_D):
        key = (vs, L, U, D)
        if key in memo:
            return memo[key]
        if len(vs) == 1:
            res = L <= lim_L and U <= lim_U and D <= lim_D
        else:
            res = False
            if D + 1 <= lim_D:
                for lower, upper in get_splits(vs):
                    if L + 1 <= lim_L and good(lower, L + 1, U, D + 1, lim_L, lim_U, lim_D) and \
                            U + 1 <= lim_U and good(upper, L, U + 1, D + 1, lim_L, lim_U, lim_D):
                        res = True
                        break
        memo[key] = res
        return res

    exists_ok = good(tuple(range(n)), 0, 0, 0, cupmax - 1, capmax - 1, strongmax - 1)
    memo.clear()
    exists_ok_swap = good(tuple(range(n)), 0, 0, 0, capmax - 1, cupmax - 1, strongmax - 1)
    return {"cupmax": cupmax, "capmax": capmax, "strongmax": strongmax, "worst": worst,
            "all": all_ok, "all_swap": all_ok_swap, "exists": exists_ok, "exists_swap": exists_ok_swap}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=7)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    class_masks, tindex = enumerate_class(args.max_n, progress=False)
    stats = {}
    examples = {}
    for n in range(3, args.max_n + 1):
        c = Counter()
        for mask in sorted(class_masks[n]):
            chi = coloring_dict(mask, n, tindex[n])
            r = analyze(chi, n, class_masks, tindex)
            c["colorings"] += 1
            for key in ("all", "all_swap", "exists", "exists_swap"):
                if r[key]:
                    c[key] += 1
                elif key not in examples.get(n, {}):
                    examples.setdefault(n, {})[key] = {"mask": mask, **r}
        stats[n] = dict(c)
        print(json.dumps({"n": n, **dict(c)}), flush=True)
    if args.output:
        args.output.write_text(json.dumps({"stats": stats, "examples": examples}, indent=1) + "\n")
    for n, ex in examples.items():
        for key, r in ex.items():
            print(f"n={n} first failure of {key}: {json.dumps(r)}")


if __name__ == "__main__":
    main()
