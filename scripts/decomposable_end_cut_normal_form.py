#!/usr/bin/env python3
"""Is the context bound always attained by an end-singleton cut?

bound(σ) is the maximum over all interval cuts (any contiguous block of the child positions,
both orientations, all couplings) of the two part bounds.  If the maximum is always attained
by a cut that isolates the *first* or the *last* child position (either side, some coupling),
every cut tree can be normalized to a sequence of end strips, and the exchange lemma behind
the additivity conjectures becomes a commutation of two end strips (experiment 0124).
Tests every context of the additivity enumeration with at least two runs (single runs have
no cuts); literal Lean recursion.  Records how often an end cut attains the bound, how often
a prefix/suffix cut of any length does, and examples where neither does.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import decomposable_recursive_formula as drf  # noqa: E402
from decomposable_additivity_test import child, contexts  # noqa: E402
from decomposable_recursive_formula import run_index  # noqa: E402


def cut_value(F, word, maxima, block, orientation, d, k):
    rest = frozenset(i for i, w in enumerate(word) if w == "S") - block
    if orientation == "lower":
        return F(*child(word, maxima, block, "lower", d)) + F(*child(word, maxima, rest, "upper", k - 1 - d))
    return F(*child(word, maxima, block, "upper", k - 1 - d)) + F(*child(word, maxima, rest, "lower", d))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--s-max", type=int, default=4)
    ap.add_argument("--e-max", type=int, default=2)
    ap.add_argument("--levels", type=int, default=2)
    ap.add_argument("--cache-size", type=int, default=1_500_000)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    a, u, k = map(int, args.case.split(","))
    drf.CACHE_SIZE = args.cache_size
    F = drf.make_F2(a, u, k, include_zero_children=True)
    stats = collections.Counter()
    examples = collections.defaultdict(list)
    for word, maxima in contexts(args.s_max, args.e_max, args.levels, k):
        pos = [i for i, w in enumerate(word) if w == "S"]
        ridx = run_index(word)
        nruns = len({ridx[p] for p in pos})
        if nruns < 2:
            continue
        b = F(word, maxima)
        stats["contexts"] += 1
        stats[f"runs{nruns}_contexts"] += 1
        if b == 0:
            stats["zero_bound"] += 1
            continue
        n = len(pos)
        best_end = 0
        best_boundary = 0
        best_interior = 0
        for i in range(n):
            for j in range(i + 1, n + 1):
                if j - i == n:
                    continue
                block = frozenset(pos[i:j])
                is_end = (i == 0 and j == 1) or (i == n - 1 and j == n) or (i == 0 and j == n - 1) or (i == 1 and j == n)
                is_boundary = i == 0 or j == n
                for o in ("lower", "upper"):
                    for d in range(1, k - 1):
                        val = cut_value(F, word, maxima, block, o, d, k)
                        if is_end:
                            best_end = max(best_end, val)
                        if is_boundary:
                            best_boundary = max(best_boundary, val)
                        else:
                            best_interior = max(best_interior, val)
        assert max(best_boundary, best_interior) == b
        stats["end_attains"] += best_end == b
        stats["boundary_attains"] += best_boundary == b
        stats[f"runs{nruns}_end_attains"] += best_end == b
        if best_end < b:
            key = "boundary_only" if best_boundary == b else "interior_only"
            stats[key] += 1
            if len(examples[key]) < 12:
                examples[key].append({"word": [w if w == "S" else [w[0], w[1]] for w in word], "maxima": list(maxima), "runs": nruns,
                                      "bound": b, "best_end": best_end, "best_boundary": best_boundary, "best_interior": best_interior})
    out = {"case": args.case, "parameters": vars(args) | {"output": str(args.output)}, "stats": dict(sorted(stats.items())), "examples": examples}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1, default=list) + "\n")
    print(json.dumps({"case": args.case, **dict(sorted(stats.items()))}), file=sys.stderr)


if __name__ == "__main__":
    main()
