#!/usr/bin/env python3
"""Enumerate the decomposable colorings that avoid an a-cap, a u-cup and a
strong k-set, exactly, by the split recursion of experiment 0114 restricted
to the avoiding subclass (hereditary: every part of an avoiding decomposable
coloring is avoiding), with the union lemma of experiments 0116/0117 used to
reject a candidate union in O(n^2) from its parts' chain tables:

  longest cup of L ∪ U  = max(longest cup of U, max over cups C of L of
                          |C| + [a U-vertex lies left of first(C)] + [one lies right of last(C)]),
  longest cap           = mirror image,
  largest strong set    = max(strong(L), strong(U), longest cup of L + longest cap of U).

Per coloring the tables of longest cups and caps by first and last vertex
and the largest strong set are kept (numpy int8), which is what the
extremal-table scripts consume.  The full class through n = 9 has 3.8 M
members; the (4,5,6)-avoiding subclass through n = 10 has a few thousand.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import triple_index, coloring_dict, strong_sizes, threshold  # noqa: E402


def chain_table(chi, n, left):
    T = np.zeros((n, n), dtype=np.int8)
    for v in range(n):
        T[v][v] = 1
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
            for f, v in best.items():
                T[f][j] = max(T[f][j], v)
    return T


def tables_for(mask, n, idx):
    if n == 1:
        return (np.ones((1, 1), dtype=np.int8), np.ones((1, 1), dtype=np.int8), 1)
    if n == 2:
        t = np.array([[1, 2], [0, 1]], dtype=np.int8)
        return (t, t.copy(), 2)
    chi = coloring_dict(mask, n, idx)
    return (chain_table(chi, n, True), chain_table(chi, n, False), strong_sizes(chi, n))


def enumerate_avoiding(a: int, u: int, k: int, max_n: int, progress=True):
    """{m: {mask: (cupT, capT, strongmax)}} for 1 <= m <= max_n."""
    classes = {1: {0: tables_for(0, 1, None)}, 2: {0: tables_for(0, 2, None)}}
    tindex = {m: triple_index(m) for m in range(1, max_n + 1)}
    for m in range(3, max_n + 1):
        started = time.time()
        idx = tindex[m]
        found = {}
        candidates = 0
        for lower_bits in range(1, (1 << m) - 1):
            lower = [v for v in range(m) if lower_bits >> v & 1]
            upper = [v for v in range(m) if not lower_bits >> v & 1]
            nl, nu = len(lower), len(upper)
            if not classes[nl] or not classes[nu]:
                continue
            # positional extension flags of L's cups by U-vertices, and of U's caps by L-vertices
            u_left = np.array([any(x < v for x in upper) for v in lower], dtype=np.int8)
            u_right = np.array([any(x > v for x in upper) for v in lower], dtype=np.int8)
            l_left = np.array([any(x < v for x in lower) for v in upper], dtype=np.int8)
            l_right = np.array([any(x > v for x in lower) for v in upper], dtype=np.int8)
            cross_left = 0
            for (i, j, kk), pos in idx.items():
                inl = (lower_bits >> i & 1) + (lower_bits >> j & 1) + (lower_bits >> kk & 1)
                if inl in (1, 2) and lower_bits >> j & 1:
                    cross_left |= 1 << pos
            tl = [idx[(lower[x], lower[y], lower[z])] for x, y, z in itertools.combinations(range(nl), 3)]
            tu = [idx[(upper[x], upper[y], upper[z])] for x, y, z in itertools.combinations(range(nu), 3)]

            def lift(mask, table):
                out = 0
                p = 0
                while mask:
                    if mask & 1:
                        out |= 1 << table[p]
                    mask >>= 1
                    p += 1
                return out

            lowers = [(lift(x, tl), cupT, capT, st) for x, (cupT, capT, st) in classes[nl].items()]
            uppers = [(lift(x, tu), cupT, capT, st) for x, (cupT, capT, st) in classes[nu].items()]
            for xl, cupL, capL, stL in lowers:
                ext_cup_L = int((cupL + u_left[:, None] + u_right[None, :]).max()) if nl >= 1 else 0
                cupmaxL = int(cupL.max())
                capmaxL = int(capL.max())
                if capmaxL >= a or ext_cup_L >= u:
                    continue
                for xu, cupU, capU, stU in uppers:
                    candidates += 1
                    capmaxU = int(capU.max())
                    if int((capU + l_left[:, None] + l_right[None, :]).max()) >= a:
                        continue
                    if int(cupU.max()) >= u:
                        continue
                    if max(stL, stU, cupmaxL + capmaxU) >= k:
                        continue
                    mask = cross_left | xl | xu
                    if mask not in found:
                        found[mask] = None
        for mask in found:
            found[mask] = tables_for(mask, m, idx)
        classes[m] = found
        if progress:
            print(f"({a},{u},{k})-avoiding n={m}: {len(found)} colorings from {candidates} candidates ({time.time()-started:.1f}s)", file=sys.stderr, flush=True)
        if not found:
            break
    return classes, tindex


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True, help="a,u,k")
    parser.add_argument("--max-n", type=int, default=10)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--validate", action="store_true", help="cross-check counts against the full class enumerator for n <= 8")
    args = parser.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    classes, tindex = enumerate_avoiding(a, u, k, args.max_n)
    counts = {m: len(c) for m, c in classes.items()}
    out = {"case": [a, u, k], "threshold": threshold(a, u, k), "counts": counts, "validation": None,
           "masks": {m: sorted(c) for m, c in classes.items() if m >= 3}}
    if args.validate:
        from enumerate_decomposable_colorings import enumerate_class, chain_profiles
        full, tfull = enumerate_class(min(8, args.max_n), progress=False)
        val = {}
        for m in range(3, min(8, args.max_n) + 1):
            idx = tfull[m]
            expected = set()
            for mask in full[m]:
                chi = coloring_dict(mask, m, idx)
                _, _, maxcup = chain_profiles(chi, m, True)
                _, _, maxcap = chain_profiles(chi, m, False)
                if maxcap < a and maxcup < u and strong_sizes(chi, m) < k:
                    expected.add(mask)
            val[m] = {"expected": len(expected), "enumerated": counts.get(m, 0), "equal": expected == set(classes.get(m, {}))}
            print(f"validate n={m}: {val[m]}", file=sys.stderr, flush=True)
        out["validation"] = val
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out) + "\n")
    print(json.dumps({"case": [a, u, k], "counts": counts}), file=sys.stderr)


if __name__ == "__main__":
    main()
