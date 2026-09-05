#!/usr/bin/env python3
"""Workstream B, step 2 (first level): positional extremal tables of the
decomposable class under one-sided external points.

A deep-below split S = L (lower) ∪ U (upper), interleaved in sweep order,
colors a mixed triple left exactly when its middle vertex is in L.  Reading
that rule off the four-vertex law gives an exact description of the union:

* caps of S are caps of L, or caps of U extended by an L-vertex on each side
  on which some L-vertex lies beyond the cap (cups: symmetric);
* strong sets of S are strong sets of L or U, or a cup of L together with a
  cap of U (any positions), so the strong sets do not depend on the
  interleaving at all;

so what a child sees of its sibling is the pair of gaps (in the child's own
sweep order) holding the sibling's first and last vertex, plus the sibling's
longest cap (for L) or cup (for U).  This script (1) verifies the description
against every deep-below split of every decomposable coloring on at most
--max-n vertices, (2) computes the resulting positional extremal function
E_low(a,u,k,c; g1,g2) = the largest decomposable L with no a-cap, no strong
k-set, cups of length at most c (the strong coupling with U's longest cap
d = k-1-c) and every cup C satisfying |C| + [first(C) >= g1] + [last(C) < g2]
<= u-1, together with the symmetric E_up, for every (a,u,k) whose threshold is
at most --max-n + 1, and (3) compares E_low with the scalar guess
decomposableThreshold(a, min(c+1, u-1-ext), k) where ext counts the sides on
which every cup is extended, listing the states where the guess is wrong.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import enumerate_class, coloring_dict, strong_sizes, threshold  # noqa: E402


def chain_first_last(chi, n, left):
    """longest[(f, l)] = longest chain of color ``left`` with first vertex f and
    last vertex l (single vertices count 1, pairs 2)."""
    end = {}
    for j in range(n):
        for i in range(j):
            best = {i: 2}
            for h in range(i):
                if chi[(h, i, j)] == left:
                    for f, v in end[(h, i)].items():
                        if v + 1 > best.get(f, 0):
                            best[f] = v + 1
            end[(i, j)] = best
    longest = {(v, v): 1 for v in range(n)}
    for (i, j), table in end.items():
        for f, v in table.items():
            longest[(f, j)] = max(longest.get((f, j), 0), v)
    return longest


def analyze(mask, n, idx):
    chi = coloring_dict(mask, n, idx)
    cups = chain_first_last(chi, n, True)
    caps = chain_first_last(chi, n, False)
    return {"chi": chi, "n": n, "cups": cups, "caps": caps,
            "maxcup": max(cups.values()), "maxcap": max(caps.values()),
            "strong": strong_sizes(chi, n)}


def positional_max(chains, n, g1, g2):
    """Largest |C| + [first >= g1] + [last < g2] over chains C."""
    return max(v + (f >= g1) + (l < g2) for (f, l), v in chains.items())


def split_ok(chi, n, lower_bits):
    for (i, j, k), c in chi.items():
        inl = [lower_bits >> v & 1 for v in (i, j, k)]
        if 0 < sum(inl) < 3 and c != bool(inl[1]):
            return False
    return True


def verify_union_description(records, tindex, max_n):
    """Every deep-below split of every coloring satisfies the union lemmas."""
    checked = 0
    for n in range(2, max_n + 1):
        idx = tindex[n]
        for rec in records[n]:
            chi = rec["chi"]
            for lower_bits in range(1, (1 << n) - 1):
                if not split_ok(chi, n, lower_bits):
                    continue
                L = [v for v in range(n) if lower_bits >> v & 1]
                U = [v for v in range(n) if not lower_bits >> v & 1]
                subL = restrict(chi, L)
                subU = restrict(chi, U)
                # gaps of U's first/last vertex inside L, and of L's inside U
                g1 = sum(1 for v in L if v < U[0]); g2 = sum(1 for v in L if v < U[-1])
                h1 = sum(1 for v in U if v < L[0]); h2 = sum(1 for v in U if v < L[-1])
                pred_cup = max(positional_max(subL["cups"], len(L), g1, g2), subU["maxcup"])
                pred_cap = max(positional_max(subU["caps"], len(U), h1, h2), subL["maxcap"])
                pred_strong = max(subL["strong"], subU["strong"], subL["maxcup"] + subU["maxcap"])
                if n >= 3:
                    assert pred_cup == rec["maxcup"], (n, mask_of(rec), lower_bits, pred_cup, rec["maxcup"])
                    assert pred_cap == rec["maxcap"], (n, lower_bits, pred_cap, rec["maxcap"])
                if n >= 4:
                    assert pred_strong == rec["strong"], (n, lower_bits, pred_strong, rec["strong"])
                checked += 1
    return checked


def mask_of(rec):
    return rec.get("mask")


def restrict(chi, vertices):
    index = {v: i for i, v in enumerate(vertices)}
    n = len(vertices)
    sub = {(index[i], index[j], index[k]): chi[(i, j, k)] for i, j, k in itertools.combinations(vertices, 3)}
    cups = chain_first_last(sub, n, True)
    caps = chain_first_last(sub, n, False)
    return {"chi": sub, "n": n, "cups": cups, "caps": caps, "maxcup": max(cups.values()),
            "maxcap": max(caps.values()), "strong": strong_sizes(sub, n) if n >= 3 else n}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=7)
    parser.add_argument("--max-k", type=int, default=6)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--skip-verify", action="store_true")
    args = parser.parse_args()
    started = time.time()
    classes, tindex = enumerate_class(args.max_n, progress=False)
    records = {}
    for n in range(1, args.max_n + 1):
        idx = tindex[n]
        recs = []
        for mask in classes[n]:
            if n >= 3:
                rec = analyze(mask, n, idx)
            else:
                rec = {"chi": {}, "n": n, "cups": {(v, v): 1 for v in range(n)}, "caps": {(v, v): 1 for v in range(n)},
                       "maxcup": n, "maxcap": n, "strong": n}
                if n == 2:
                    rec["cups"][(0, 1)] = 2; rec["caps"][(0, 1)] = 2
            rec["mask"] = mask
            recs.append(rec)
        records[n] = recs
    print(f"class enumerated to n={args.max_n}: {[len(records[n]) for n in records]} ({time.time()-started:.0f}s)", file=sys.stderr, flush=True)
    result = {"max_n": args.max_n, "verified_splits": None, "tables": {}}
    if not args.skip_verify:
        result["verified_splits"] = verify_union_description(records, tindex, args.max_n)
        print(f"union description verified on {result['verified_splits']} splits ({time.time()-started:.0f}s)", file=sys.stderr, flush=True)

    keys = [(a, u, k) for a in range(3, args.max_k + 1) for u in range(3, args.max_k + 1)
            for k in range(max(a, u, 4), args.max_k + 1) if threshold(a, u, k) <= args.max_n + 1]
    for (a, u, k) in keys:
        T = threshold(a, u, k)
        low = {}
        up = {}
        mismatches = []
        for c in range(1, k):          # cups of L at most c; U's caps at most d = k-1-c
            for n in range(1, args.max_n + 1):
                for g1 in range(n + 1):
                    for g2 in range(g1, n + 1):
                        ok = any(rec["maxcap"] <= a - 1 and rec["strong"] <= k - 1 and rec["maxcup"] <= c
                                 and positional_max(rec["cups"], n, g1, g2) <= u - 1 for rec in records[n])
                        if ok:
                            low[(c, g1, g2)] = max(low.get((c, g1, g2), 0), n)
        for d in range(1, k):
            for n in range(1, args.max_n + 1):
                for h1 in range(n + 1):
                    for h2 in range(h1, n + 1):
                        ok = any(rec["maxcup"] <= u - 1 and rec["strong"] <= k - 1 and rec["maxcap"] <= d
                                 and positional_max(rec["caps"], n, h1, h2) <= a - 1 for rec in records[n])
                        if ok:
                            up[(d, h1, h2)] = max(up.get((d, h1, h2), 0), n)
        # scalar guess: every cup extended on ext sides, ext = [g1 == 0] + [g2 == n]  (n unknown: use g2 >= value)
        table_low = {}
        for (c, g1, g2), value in sorted(low.items()):
            ext = (1 if g1 == 0 else 0) + (1 if g2 >= value else 0)
            guess = threshold(a, min(c + 1, u - ext), k) if min(c + 1, u - ext) >= 2 else 1
            table_low[f"c={c},g1={g1},g2={g2}"] = {"E_low": value, "guess": guess}
            if guess != value:
                mismatches.append({"side": "low", "c": c, "g1": g1, "g2": g2, "E": value, "guess": guess})
        table_up = {}
        for (d, h1, h2), value in sorted(up.items()):
            ext = (1 if h1 == 0 else 0) + (1 if h2 >= value else 0)
            guess = threshold(min(d + 1, a - ext), u, k) if min(d + 1, a - ext) >= 2 else 1
            table_up[f"d={d},h1={h1},h2={h2}"] = {"E_up": value, "guess": guess}
            if guess != value:
                mismatches.append({"side": "up", "d": d, "h1": h1, "h2": h2, "E": value, "guess": guess})
        # top-level closure: max over consistent pairs of E_low + E_up against T
        best = 0
        best_state = None
        for (c, g1, g2), m in low.items():
            d = k - 1 - c
            for (dd, h1, h2), mm in up.items():
                if dd > d:
                    continue
                # consistency of the interleaving: exactly one part comes first, exactly one comes last
                first_ok = (g1 == 0) != (h1 == 0)
                last_ok = (g2 == m) != (h2 == mm)
                if not (first_ok and last_ok):
                    continue
                if m + mm > best:
                    best, best_state = m + mm, {"c": c, "g": [g1, g2], "d": dd, "h": [h1, h2], "sizes": [m, mm]}
        result["tables"][f"{a},{u},{k}"] = {"threshold": T, "top_closure_max": best, "top_closure_state": best_state,
                                            "E_low": table_low, "E_up": table_up,
                                            "scalar_guess_mismatches": mismatches}
        print(json.dumps({"a": a, "u": u, "k": k, "threshold": T, "top_closure_max": best,
                          "mismatches": len(mismatches)}), file=sys.stderr, flush=True)
    result["seconds"] = round(time.time() - started, 1)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=1) + "\n")


if __name__ == "__main__":
    main()
