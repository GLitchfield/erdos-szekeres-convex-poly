#!/usr/bin/env python3
"""Which prefix/suffix cut dominates a crossing partition of a two-run context?

For every well-formed context with exactly two child runs and every partition whose
membership pattern along the child positions has a given number of blocks (4 = A-B-A-B,
the first milestone of the two-run boundary-domination lemma), record, for each
orientation o and coupling d, the set of (I, d') with I a prefix or suffix and
V(K, o, d) <= V(I, o, d'), and summarize what the dominating cuts look like:
whether the original coupling d' = d works, the smallest |d' - d| that works, whether
the cut at the run boundary works, and whether the cut just before the first or after the
last position of the kept part works.  Literal Lean recursion (zero-valued children kept).
"""
from __future__ import annotations

import argparse
import collections
import itertools
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import decomposable_recursive_formula as drf  # noqa: E402
from decomposable_additivity_test import child, contexts  # noqa: E402
from decomposable_recursive_formula import run_index  # noqa: E402


def split_value(F, word, maxima, keep, orientation, d, k):
    rest = frozenset(i for i, w in enumerate(word) if w == "S") - keep
    if orientation == "lower":
        return F(*child(word, maxima, keep, "lower", d)) + F(*child(word, maxima, rest, "upper", k - 1 - d))
    return F(*child(word, maxima, keep, "upper", k - 1 - d)) + F(*child(word, maxima, rest, "lower", d))


def blocks_of(pattern):
    n = 1
    for a, b in zip(pattern, pattern[1:]):
        n += a != b
    return n


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--s-max", type=int, default=4)
    ap.add_argument("--e-max", type=int, default=2)
    ap.add_argument("--levels", type=int, default=2)
    ap.add_argument("--blocks", type=int, default=4, help="membership blocks of the partition along the positions (4 = A-B-A-B); 0 = any")
    ap.add_argument("--cache-size", type=int, default=1_500_000)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    a, u, k = map(int, args.case.split(","))
    drf.CACHE_SIZE = args.cache_size
    F = drf.make_F2(a, u, k, include_zero_children=True)
    stats = collections.Counter()
    examples = collections.defaultdict(list)
    cover_sets: list[frozenset] = []
    ncontexts = 0
    for word, maxima in contexts(args.s_max, args.e_max, args.levels, k):
        pos = [i for i, w in enumerate(word) if w == "S"]
        ridx = run_index(word)
        if len({ridx[p] for p in pos}) != 2:
            continue
        ncontexts += 1
        n = len(pos)
        boundary = ridx.index(1) if 1 in ridx else None  # first position of run 2 (word index)
        run_cut_j = sum(1 for p in pos if ridx[p] == 0)  # prefix length at the run boundary
        cuts = [("prefix", j, frozenset(pos[:j])) for j in range(1, n)] + [("suffix", j, frozenset(pos[j:])) for j in range(1, n)]
        table = {}
        for name, j, I in cuts:
            for o in ("lower", "upper"):
                for d2 in range(1, k - 1):
                    table[name, j, o, d2] = split_value(F, word, maxima, I, o, d2, k)
        for mask in range(1, (1 << n) - 1):
            pattern = [(mask >> t) & 1 for t in range(n)]
            keep = frozenset(p for t, p in enumerate(pos) if pattern[t])
            nb = blocks_of(pattern)
            if args.blocks and nb != args.blocks:
                continue
            if nb <= 2:
                continue  # a prefix/suffix cut itself
            first_keep = min(t for t in range(n) if pattern[t]); last_keep = max(t for t in range(n) if pattern[t])
            for o in ("lower", "upper"):
                for d in range(1, k - 1):
                    stats["splits"] += 1
                    v = split_value(F, word, maxima, keep, o, d, k)
                    dom = [(name, j, d2) for (name, j, o2, d2), val in table.items() if o2 == o and val >= v]
                    if not dom:
                        stats["undominated"] += 1
                        if len(examples["undominated"]) < 10:
                            examples["undominated"].append({"word": word, "maxima": list(maxima), "keep": sorted(keep), "o": o, "d": d, "value": v})
                        continue
                    same_d = [x for x in dom if x[2] == d]
                    stats["dominated"] += 1
                    stats["same_coupling_works"] += bool(same_d)
                    stats["min_recoupling_" + str(min(abs(x[2] - d) for x in dom))] += 1
                    stats["run_boundary_prefix_works"] += any(x[0] == "prefix" and x[1] == run_cut_j for x in dom)
                    stats["run_boundary_either_works"] += any(x[1] == run_cut_j for x in dom)
                    stats["cut_before_first_keep_works"] += any(x[0] == "prefix" and x[1] == first_keep for x in dom) if first_keep > 0 else 0
                    stats["cut_after_last_keep_works"] += any(x[0] == "suffix" and x[1] == last_keep + 1 for x in dom) if last_keep < n - 1 else 0
                    stats["singleton_end_works"] += any(x[1] in (1, n - 1) for x in dom)
                    # which end, at which coupling: the first position alone (prefix 1) or the last alone (suffix n-1)
                    first_alone = [x for x in dom if x[0] == "prefix" and x[1] == 1]
                    last_alone = [x for x in dom if x[0] == "suffix" and x[1] == n - 1]
                    stats["first_alone_works"] += bool(first_alone)
                    stats["last_alone_works"] += bool(last_alone)
                    stats["first_alone_same_d"] += any(x[2] == d for x in first_alone)
                    stats["last_alone_same_d"] += any(x[2] == d for x in last_alone)
                    stats["some_end_alone_same_d"] += any(x[2] == d for x in first_alone + last_alone)
                    if first_alone or last_alone:
                        best_shift = min(abs(x[2] - d) for x in first_alone + last_alone)
                        stats[f"end_alone_min_shift_{best_shift}"] += 1
                        signs = {("+" if x[2] > d else "-" if x[2] < d else "0") for x in first_alone + last_alone if abs(x[2] - d) == best_shift}
                        stats["end_alone_shift_sign_" + "".join(sorted(signs))] += 1
                    # the kept part's own end: is the first kept position at an end of the child?
                    stats["keep_touches_end"] += (first_keep == 0 or last_keep == n - 1)
                    # an end singleton or the run-boundary cut: enough for every split?
                    stats["end_or_runboundary_works"] += bool(first_alone or last_alone or any(x[1] == run_cut_j for x in dom))
                    # cut positions (prefix length j, either kind) that dominate this split, for a set cover per case
                    cover_sets.append(frozenset(x[1] for x in dom))
                    if not (first_alone or last_alone or any(x[1] == run_cut_j for x in dom)) and len(examples["needs_other_position"]) < 12:
                        examples["needs_other_position"].append({"word": word, "maxima": list(maxima), "keep": sorted(keep), "o": o, "d": d, "value": v,
                                                                 "dominating": sorted(dom)[:8], "run_boundary_j": run_cut_j, "n": n})
                    stats["d_prime_le_d_works"] += any(x[2] <= d for x in dom)
                    stats["d_prime_ge_d_works"] += any(x[2] >= d for x in dom)
                    if not same_d and len(examples["needs_recoupling"]) < 12:
                        examples["needs_recoupling"].append({"word": word, "maxima": list(maxima), "keep": sorted(keep), "o": o, "d": d, "value": v,
                                                             "dominating": sorted(dom)[:8], "run_boundary_j": run_cut_j})
    # greedy set cover: how many distinct prefix lengths (relative to n) are needed so that every split is
    # dominated by a cut at one of them; positions are recorded as (j, n) pairs
    out = {"case": args.case, "parameters": {"s_max": args.s_max, "e_max": args.e_max, "levels": args.levels, "blocks": args.blocks},
           "two_run_contexts": ncontexts, "stats": dict(stats), "examples": examples,
           "splits_dominated_only_by_interior_cuts": sum(1 for cs in cover_sets if cs and not any(j in (1,) or j >= 0 and False for j in cs))}
    out["splits_with_single_dominating_position"] = sum(1 for cs in cover_sets if len(cs) == 1)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1, default=list) + "\n")
    print(json.dumps({"case": args.case, "contexts": ncontexts, **{k_: v for k_, v in stats.items()}}), file=sys.stderr)


if __name__ == "__main__":
    main()
