#!/usr/bin/env python3
"""The strip inequality, leaf by leaf (experiment 0124 §4, item 1 of the 7 September plan).

For an interior cut (B, o, d) of a context with at least two runs, the interior-first tree is
"cut B, then strip the rest part R at its optimal end e on side s at coupling m"; the mirror
end-first tree is "strip e on side s at coupling m at the root, then cut B in the residual σ'
at coupling d".  Writing E1, E2 for the two contexts of the singleton {e}, A, A' for the two
contexts of the block B, and R', R'' for the two residual contexts of rest ∖ {e}, the totals
are

    V1 = base(A) + base(E1) + bound(R')      V2 = base(E2) + base(A') + bound(R'').

This script records, for every interior cut whose rest part has an optimal end strip with a
multi-run residual, the pair comparison base(A) + base(E1) <= base(E2) + base(A'), the
residual comparison bound(R') <= bound(R''), the cup/cap limits of the four single-run leaves
(the numbers a numeric lemma would be stated in), and the totals, so that the shape of the
Lean lemma can be read off.  Literal Lean recursion.
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
from decomposable_depth2_tables import limits_from_signature  # noqa: E402
from decomposable_recursive_formula import run_index  # noqa: E402


def leaf_limits(word, maxima, a, u, k):
    """(runs, cup limit, cap limit) of a context at its head position, as the base uses them."""
    p, cu, ca = limits_from_signature(word, maxima, a, u, k, lean=True)
    return p, int(cu[0][0]), int(ca[0][0])


def cut(F, word, maxima, block, o, d, k):
    rest = frozenset(i for i, w in enumerate(word) if w == "S") - block
    if o == "lower":
        A = child(word, maxima, block, "lower", d); R = child(word, maxima, rest, "upper", k - 1 - d)
    else:
        A = child(word, maxima, block, "upper", k - 1 - d); R = child(word, maxima, rest, "lower", d)
    return A, R


def strip(word, maxima, p, s, m, k):
    """Strip position p on side s at coupling m: (singleton context, residual context)."""
    pos = frozenset(i for i, w in enumerate(word) if w == "S")
    if s == "lower":
        return child(word, maxima, frozenset([p]), "lower", m), child(word, maxima, pos - {p}, "upper", k - 1 - m)
    return child(word, maxima, frozenset([p]), "upper", k - 1 - m), child(word, maxima, pos - {p}, "lower", m)


def nruns(word):
    pos = [i for i, w in enumerate(word) if w == "S"]
    ridx = run_index(word)
    return len({ridx[p] for p in pos})


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
    tuples = collections.Counter()
    examples = collections.defaultdict(list)
    for word, maxima in contexts(args.s_max, args.e_max, args.levels, k):
        pos = [i for i, w in enumerate(word) if w == "S"]
        if nruns(word) < 2:
            continue
        n = len(pos)
        for i in range(1, n):
            for j in range(i + 1, n):
                B = frozenset(pos[i:j])
                for o in ("lower", "upper"):
                    for d in range(1, k - 1):
                        A, R = cut(F, word, maxima, B, o, d, k)
                        bA, bR = F(*A), F(*R)
                        v1 = bA + bR
                        stats["interior_cuts"] += 1
                        rpos = [q for q, w in enumerate(R[0]) if w == "S"]
                        # does ANY root strip (any end, side, coupling; block recut at any coupling) give a
                        # termwise decomposition, i.e. pair and residual inequalities both holding?
                        any_termwise = False; any_total = False
                        witnesses = []  # (end, s_root, m_root, d_root, s_r, m_r) with pair and residual both holding
                        for e_any in (pos[0], pos[-1]):
                            for s_any in ("lower", "upper"):
                                for m_any in range(1, k - 1):
                                    E2x, sig2x = strip(word, maxima, e_any, s_any, m_any, k)
                                    if nruns(sig2x[0]) < 2:
                                        if F(*E2x) + F(*sig2x) >= v1:
                                            any_total = True
                                        continue
                                    for d_any in range(1, k - 1):
                                        A2x, R2x = cut(F, sig2x[0], sig2x[1], B, o, d_any, k)
                                        tot = F(*E2x) + F(*A2x) + F(*R2x)
                                        if tot >= v1:
                                            any_total = True
                                        # termwise: the interior tree's rest part R is itself a max over its strips;
                                        # compare against R's optimal strip with the same end if it exists
                                        for s_r in ("lower", "upper"):
                                            for m_r in range(1, k - 1):
                                                E1x, Rpx = strip(R[0], R[1], e_any, s_r, m_r, k)
                                                if F(*E1x) + F(*Rpx) != bR:
                                                    continue
                                                if bA + F(*E1x) <= F(*E2x) + F(*A2x) and F(*Rpx) <= F(*R2x):
                                                    any_termwise = True
                                                    witnesses.append(("first" if e_any == pos[0] else "last", s_any, m_any, d_any, s_r, m_r))
                        stats["any_root_strip_dominates"] += any_total
                        stats["any_root_strip_termwise"] += any_termwise
                        stats["dominated_but_never_termwise"] += any_total and not any_termwise
                        if witnesses:
                            other = "upper" if o == "lower" else "lower"
                            rule_hits = {
                                "mirror (same side, same m, same d)": any(sr == s2 and mr == m2 and d2 == d for (_, s2, m2, d2, sr, mr) in witnesses),
                                "swap side, same m, same d": any(sr != s2 and mr == m2 and d2 == d for (_, s2, m2, d2, sr, mr) in witnesses),
                                "root side = block side o, same d": any(s2 == o and d2 == d for (_, s2, m2, d2, sr, mr) in witnesses),
                                "root side = other side, same d": any(s2 == other and d2 == d for (_, s2, m2, d2, sr, mr) in witnesses),
                                "same m, same d, any side": any(mr == m2 and d2 == d for (_, s2, m2, d2, sr, mr) in witnesses),
                                "same d, any side and m": any(d2 == d for (_, s2, m2, d2, sr, mr) in witnesses),
                                "m within 1, same d": any(abs(mr - m2) <= 1 and d2 == d for (_, s2, m2, d2, sr, mr) in witnesses),
                                "mirror or swap side (same m, same d)": any(mr == m2 and d2 == d for (_, s2, m2, d2, sr, mr) in witnesses),
                            }
                            for name, hit in rule_hits.items():
                                stats["rule: " + name] += hit
                            if not rule_hits["same m, same d, any side"] and len(examples["rule_miss"]) < 10:
                                examples["rule_miss"].append({"word": word, "maxima": list(maxima), "block": sorted(B), "o": o, "d": d, "witnesses": sorted(set(witnesses))[:8]})
                        # optimal end strips of R with a multi-run residual, in the rest part's own coordinates
                        found = False
                        for end, e in (("first", rpos[0]), ("last", rpos[-1])):
                            for s in ("lower", "upper"):
                                for m in range(1, k - 1):
                                    E1, Rp = strip(R[0], R[1], e, s, m, k)
                                    if F(*E1) + F(*Rp) != bR or nruns(Rp[0]) < 2:
                                        continue
                                    found = True
                                    # the same position in σ: rest positions keep their word indices under `child`
                                    E2, sig2 = strip(word, maxima, e, s, m, k)
                                    if nruns(sig2[0]) < 2:
                                        stats["mirror_residual_single_run"] += 1
                                        continue
                                    A2, R2 = cut(F, sig2[0], sig2[1], B, o, d, k)
                                    v2 = F(*E2) + F(*A2) + F(*R2)
                                    pair = bA + F(*E1) <= F(*E2) + F(*A2)
                                    res = F(*Rp) <= F(*R2)
                                    stats["mirror_checked"] += 1
                                    stats["mirror_total_holds"] += v1 <= v2
                                    stats["pair_holds"] += pair
                                    stats["residual_holds"] += res
                                    stats["pair_and_residual"] += pair and res
                                    stats["total_holds_not_pairwise"] += (v1 <= v2) and not (pair and res)
                                    _, clA, plA = leaf_limits(A[0], A[1], a, u, k)
                                    _, clE1, plE1 = leaf_limits(E1[0], E1[1], a, u, k)
                                    _, clE2, plE2 = leaf_limits(E2[0], E2[1], a, u, k)
                                    _, clA2, plA2 = leaf_limits(A2[0], A2[1], a, u, k)
                                    key = (o, s, d, m, clA, plA, clE1, plE1, clE2, plE2, clA2, plA2, int(pair))
                                    tuples[key] += 1
                                    if not pair and len(examples["pair_fails"]) < 12:
                                        examples["pair_fails"].append({"word": word, "maxima": list(maxima), "block": sorted(B), "o": o, "d": d,
                                                                       "strip": [end, s, m], "A": [clA, plA, bA], "E1": [clE1, plE1, F(*E1)],
                                                                       "E2": [clE2, plE2, F(*E2)], "A2": [clA2, plA2, F(*A2)],
                                                                       "res": [F(*Rp), F(*R2)], "totals": [v1, v2]})
                                    if not res and len(examples["residual_fails"]) < 12:
                                        examples["residual_fails"].append({"word": word, "maxima": list(maxima), "block": sorted(B), "o": o, "d": d,
                                                                           "strip": [end, s, m], "res": [F(*Rp), F(*R2)], "totals": [v1, v2],
                                                                           "Rp": [Rp[0], list(Rp[1])], "R2": [R2[0], list(R2[1])]})
                        if not found:
                            stats["rest_has_no_multirun_optimal_strip"] += 1
    out = {"case": args.case, "parameters": vars(args) | {"output": str(args.output)}, "stats": dict(sorted(stats.items())),
           "tuples": [{"key": list(kk), "count": c} for kk, c in sorted(tuples.items(), key=lambda t: -t[1])],
           "examples": examples}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1, default=list) + "\n")
    print(json.dumps({"case": args.case, **dict(sorted(stats.items()))}), file=sys.stderr)


if __name__ == "__main__":
    main()
