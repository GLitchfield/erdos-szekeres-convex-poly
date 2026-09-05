#!/usr/bin/env python3
"""Extremal witnesses of a depth-1 child by run structure (experiment 0118),
with their internal decomposition: for the case (a,u,k), the child side, the
number of runs p, the outer flags and the coupling, list the colorings of
maximal size that meet the constraints, and for each its run sizes, the cup
and cap maxima inside each run, and its top-level deep-below splits with the
number of vertices each part takes from each run.  Research aid for the
closed form of Workstream B step 3."""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import enumerate_class, coloring_dict, strong_sizes  # noqa: E402
from decomposable_avoiding_class import enumerate_avoiding, chain_table  # noqa: E402
from decomposable_run_extremal import compositions  # noqa: E402
from decomposable_context_functions import deep_below_split_ok, restrict_mask  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--side", choices=("lower", "upper"), default="lower")
    parser.add_argument("--runs", type=int, default=2)
    parser.add_argument("--before", type=int, default=0)
    parser.add_argument("--after", type=int, default=0)
    parser.add_argument("--coupling", type=int, default=1)
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--avoiding", action="store_true")
    parser.add_argument("--limit", type=int, default=6)
    args = parser.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    lower = args.side == "lower"
    if args.avoiding:
        classes, tindex = enumerate_avoiding(a, u, k, args.max_n, progress=False)
        tables = {m: {mask: t for mask, t in c.items()} for m, c in classes.items()}
    else:
        classes, tindex = enumerate_class(args.max_n, progress=False)
        tables = {}
        for m in range(3, args.max_n + 1):
            idx = tindex[m]
            tables[m] = {}
            for mask in classes[m]:
                chi = coloring_dict(mask, m, idx)
                tables[m][mask] = (chain_table(chi, m, True), chain_table(chi, m, False), strong_sizes(chi, m))
    p = args.runs
    found = []
    for m in range(args.max_n, p - 1, -1):
        for mask, (cupT, capT, st) in tables.get(m, {}).items():
            if st > k - 1:
                continue
            if lower and capT.max() > a - 1:
                continue
            if not lower and cupT.max() > u - 1:
                continue
            for comp in compositions(m, p):
                run = np.repeat(np.arange(p), comp)
                left_ext = (run > 0) | bool(args.before)
                right_ext = (run < p - 1) | bool(args.after)
                if lower:
                    limit = np.minimum(u - 1 - left_ext[:, None].astype(int) - right_ext[None, :].astype(int), k - 1 - args.coupling)
                    ok = (np.triu(cupT) <= np.triu(limit)).all()
                else:
                    limit = np.minimum(a - 1 - left_ext[:, None].astype(int) - right_ext[None, :].astype(int), k - 1 - args.coupling)
                    ok = (np.triu(capT) <= np.triu(limit)).all()
                if ok:
                    found.append((m, mask, comp))
        if found:
            break
    if not found:
        print("no witness"); return
    m = found[0][0]
    print(f"({a},{u},{k}) {args.side} child, p={p}, outer=({args.before},{args.after}), coupling={args.coupling}: E = {m}, {len(found)} (coloring, run-sizes) witnesses")
    idx = tindex[m]
    shown = 0
    seen_masks = set()
    for m, mask, comp in found:
        if mask in seen_masks:
            continue
        seen_masks.add(mask)
        chi = coloring_dict(mask, m, idx)
        cupT, capT, st = tables[m][mask]
        run = list(np.repeat(np.arange(p), comp))
        parts = []
        # top-level deep-below splits of this coloring with both parts decomposable
        for lower_bits in range(1, (1 << m) - 1):
            L = tuple(v for v in range(m) if lower_bits >> v & 1); U = tuple(v for v in range(m) if not lower_bits >> v & 1)
            if not deep_below_split_ok(chi, tuple(range(m)), set(L)):
                continue
            okl = restrict_mask(chi, L, {mm: set(tables.get(mm, {}).keys()) for mm in tables} | {1: {0}, 2: {0}}, tindex)[1] if len(L) >= 3 else True
            oku = restrict_mask(chi, U, {mm: set(tables.get(mm, {}).keys()) for mm in tables} | {1: {0}, 2: {0}}, tindex)[1] if len(U) >= 3 else True
            if okl and oku:
                parts.append((L, U))
        per_run = []
        for r in range(p):
            vs = [v for v in range(m) if run[v] == r]
            sub = {t: chi[t] for t in itertools.combinations(vs, 3)}
            index = {v: i for i, v in enumerate(vs)}
            sub2 = {(index[i], index[j], index[l]): c for (i, j, l), c in sub.items()}
            n_r = len(vs)
            cmax = int(chain_table(sub2, n_r, True).max()) if n_r >= 3 else n_r
            pmax = int(chain_table(sub2, n_r, False).max()) if n_r >= 3 else n_r
            per_run.append({"size": n_r, "maxcup": cmax, "maxcap": pmax})
        left = sorted(t for t, c in chi.items() if c)
        print(f"  witness: runs {comp} per-run {per_run}; maxcup {int(cupT.max())} maxcap {int(capT.max())} strong {int(st)}; left turns {left}")
        for L, U in parts[:6]:
            print(f"    split lower={L} upper={U}: lower takes {[sum(1 for v in L if run[v]==r) for r in range(p)]} from runs, upper takes {[sum(1 for v in U if run[v]==r) for r in range(p)]}")
        shown += 1
        if shown >= args.limit:
            break


if __name__ == "__main__":
    main()
