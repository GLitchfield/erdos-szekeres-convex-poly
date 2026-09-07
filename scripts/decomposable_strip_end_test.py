#!/usr/bin/env python3
"""The stripping step of the two-run boundary-domination proof (experiment 0124 §3).

For a two-run context and a partition K (orientation o, coupling d) that is not itself a
prefix/suffix cut, let p be the first (or last) child position and σ' the context obtained by
cutting p off as a prefix (or suffix) cut at coupling d'', p staying on the side its membership
gives it (the kept side if p ∈ K, the other side otherwise): σ' has the other positions as its
child, with p an external letter of the new level 1.  The induction needs

    V_σ(K, o, d) <= base(σ.part {p} o d'') + V_{σ'}(K \ {p}, o, d''')

for some admissible d'', d''' (the value of "strip p first, then partition the rest"), which is
stronger than domination by the end cut (whose right-hand side has bound(σ') in place of
V_{σ'}(K \ {p}, ...)).  Records, per membership block count, whether the step holds with
d'' = d''' = d, with |d'' - d| <= 1 and d''' = d, with both free, and for which end.
Literal Lean recursion.
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


def blocks_of(pattern):
    return 1 + sum(a != b for a, b in zip(pattern, pattern[1:]))


def value(F, word, maxima, keep, o, d, k):
    rest = frozenset(i for i, w in enumerate(word) if w == "S") - keep
    if o == "lower":
        return F(*child(word, maxima, keep, "lower", d)) + F(*child(word, maxima, rest, "upper", k - 1 - d))
    return F(*child(word, maxima, keep, "upper", k - 1 - d)) + F(*child(word, maxima, rest, "lower", d))


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
    ncontexts = 0
    for word, maxima in contexts(args.s_max, args.e_max, args.levels, k):
        pos = [i for i, w in enumerate(word) if w == "S"]
        ridx = run_index(word)
        if len({ridx[p] for p in pos}) != 2:
            continue
        ncontexts += 1
        n = len(pos)
        allpos = frozenset(pos)
        for mask in range(1, (1 << n) - 1):
            pattern = [(mask >> t) & 1 for t in range(n)]
            nb = blocks_of(pattern)
            if nb <= 2:
                continue
            keep = frozenset(p for t, p in enumerate(pos) if pattern[t])
            for o in ("lower", "upper"):
                for d in range(1, k - 1):
                    v = value(F, word, maxima, keep, o, d, k)
                    stats[f"b{nb}_splits"] += 1
                    found = {}
                    for end, p in (("first", pos[0]), ("last", pos[-1])):
                        rest = allpos - {p}
                        keep2 = keep - {p}
                        if not keep2 or keep2 == rest:
                            continue  # stripping p leaves an empty part: the partition of σ' degenerates
                        # p on the side its membership gives it (own), or on the opposite side (swap)
                        own_side = o if p in keep else ("upper" if o == "lower" else "lower")
                        for side_kind, p_side in (("own", own_side), ("swap", "upper" if own_side == "lower" else "lower")):
                            for d2 in range(1, k - 1):
                                if p_side == "lower":
                                    base_p = F(*child(word, maxima, frozenset([p]), "lower", d2))
                                    w2, m2 = child(word, maxima, rest, "upper", k - 1 - d2)
                                else:
                                    base_p = F(*child(word, maxima, frozenset([p]), "upper", k - 1 - d2))
                                    w2, m2 = child(word, maxima, rest, "lower", d2)
                                for d3 in range(1, k - 1):
                                    # the partition K \ {p} of σ' in the same orientation
                                    v2 = value(F, w2, m2, keep2, o, d3, k)
                                    if base_p + v2 >= v:
                                        found[end, side_kind, d2, d3] = base_p + v2
                    if not found:
                        stats[f"b{nb}_fails"] += 1
                        if len(examples[f"b{nb}_fail"]) < 8:
                            examples[f"b{nb}_fail"].append({"word": word, "maxima": list(maxima), "keep": sorted(keep), "o": o, "d": d, "value": v})
                        continue
                    stats[f"b{nb}_holds"] += 1
                    stats[f"b{nb}_own_side_works"] += any(sk == "own" for (_, sk, _, _) in found)
                    stats[f"b{nb}_own_side_same_d_both"] += any(sk == "own" and d2 == d and d3 == d for (_, sk, d2, d3) in found)
                    stats[f"b{nb}_swap_side_needed"] += not any(sk == "own" for (_, sk, _, _) in found)
                    stats[f"b{nb}_same_d_both"] += any(d2 == d and d3 == d for (_, _, d2, d3) in found)
                    stats[f"b{nb}_first_works"] += any(e == "first" for (e, _, _, _) in found)
                    stats[f"b{nb}_last_works"] += any(e == "last" for (e, _, _, _) in found)
                    if not any(sk == "own" for (_, sk, _, _) in found) and len(examples[f"b{nb}_swap_needed"]) < 8:
                        examples[f"b{nb}_swap_needed"].append({"word": word, "maxima": list(maxima), "keep": sorted(keep), "o": o, "d": d, "value": v,
                                                               "found": sorted((e, sk, d2, d3, val) for (e, sk, d2, d3), val in found.items())[:8]})
    out = {"case": args.case, "parameters": vars(args) | {"output": str(args.output)}, "two_run_contexts": ncontexts,
           "stats": dict(sorted(stats.items())), "examples": examples}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1, default=list) + "\n")
    print(json.dumps({"case": args.case, "contexts": ncontexts, **dict(sorted(stats.items()))}), file=sys.stderr)


if __name__ == "__main__":
    main()
