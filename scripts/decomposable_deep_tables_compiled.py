#!/usr/bin/env python3
"""Deep signature tables (experiment 0119) from a compiled class: for extremal colorings
of a case read from tools/decomp_enum/enum_avoid output, enumerate the subtrees of all
decomposition trees (membership tested against the compiled classes), collect their
context signatures, and compute the exact extremal value E of each signature by the
numpy scan over the compiled class.  Output has the same shape as
decomposable_depth2_tables.py, so decomposable_recursive_formula.py compares F / F2
against it.  --samples limits the number of extremal colorings (random, seeded)."""
from __future__ import annotations

import argparse
import itertools
import json
import random
import sys
import time
from collections import defaultdict
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import threshold  # noqa: E402
from decomposable_context_functions import path_levels, deep_below_split_ok  # noqa: E402
from decomposable_depth2_tables import signature, limits_from_signature  # noqa: E402
from decomposable_run_extremal import compositions  # noqa: E402

MASKW = 9


def load(class_dir: Path, max_n: int):
    masks = {}      # m -> set of python ints (membership)
    data = {}       # m -> (cups, caps, strong) arrays
    for m in range(1, max_n + 1):
        if m <= 2:
            t = np.triu(np.full((m, m), 2, dtype=np.int8)); np.fill_diagonal(t, 1)
            data[m] = (t[None], t[None].copy(), np.array([m], dtype=np.int8)); masks[m] = {0}; continue
        f = class_dir / f"class_{m}.bin"
        rec = MASKW * 8 + 2 * m * m + 4
        if not f.exists() or f.stat().st_size == 0:
            data[m] = None; masks[m] = set(); continue
        raw = np.fromfile(f, dtype=np.uint8)
        count = raw.size // rec
        recs = raw.reshape(count, rec)
        words = recs[:, :MASKW * 8].copy().view(np.uint64).reshape(count, MASKW)
        ms = set()
        for row in words:
            v = 0
            for i, w in enumerate(row):
                v |= int(w) << (64 * i)
            ms.add(v)
        masks[m] = ms
        cups = recs[:, MASKW * 8: MASKW * 8 + m * m].astype(np.int8).reshape(count, m, m)
        caps = recs[:, MASKW * 8 + m * m: MASKW * 8 + 2 * m * m].astype(np.int8).reshape(count, m, m)
        data[m] = (cups, caps, recs[:, -4].astype(np.int8))
    return masks, data


def tri_index(n):
    return {t: i for i, t in enumerate(itertools.combinations(range(n), 3))}


def restrict_mask(chi, vertices, idx_m):
    mask = 0
    for (a, b, c), pos in idx_m.items():
        if chi[(vertices[a], vertices[b], vertices[c])]:
            mask |= 1 << pos
    return mask


def subtrees(chi, n, masks, tindex):
    seen = {tuple(range(n)): None}
    stack = [tuple(range(n))]
    while stack:
        vs = stack.pop()
        if len(vs) == 1:
            continue
        for lower_bits in range(1, (1 << len(vs)) - 1):
            lower = tuple(v for i, v in enumerate(vs) if lower_bits >> i & 1)
            upper = tuple(v for i, v in enumerate(vs) if not lower_bits >> i & 1)
            if not deep_below_split_ok(chi, vs, set(lower)):
                continue
            if len(lower) >= 3 and restrict_mask(chi, lower, tindex[len(lower)]) not in masks[len(lower)]:
                continue
            if len(upper) >= 3 and restrict_mask(chi, upper, tindex[len(upper)]) not in masks[len(upper)]:
                continue
            for part, side in ((lower, "lower"), (upper, "upper")):
                if part not in seen:
                    seen[part] = (vs, side); stack.append(part)
    return seen


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--class-dir", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=0, help="0 = all extremal colorings")
    parser.add_argument("--seed", type=int, default=20260907)
    parser.add_argument("--min-depth", type=int, default=2)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    T = threshold(a, u, k)
    started = time.time()
    masks, data = load(args.class_dir, T)
    tindex = {m: tri_index(m) for m in range(1, T + 1)}
    print(json.dumps({"loaded": {m: len(masks[m]) for m in masks}, "seconds": round(time.time() - started)}), file=sys.stderr, flush=True)
    extremal = sorted(masks[T])
    rng = random.Random(args.seed)
    if args.samples and args.samples < len(extremal):
        extremal = rng.sample(extremal, args.samples)
    sigs = {}
    idxT = tindex[T]
    for count, mask in enumerate(extremal, 1):
        chi = {t: bool(mask >> p & 1) for t, p in idxT.items()}
        seen = subtrees(chi, T, masks, tindex)
        for S in seen:
            if len(S) < 3 or len(S) == T:
                continue
            levels = path_levels(seen, S)
            if len(levels) < args.min_depth:
                continue
            word, maxima = signature(chi, T, S, levels)
            rec = sigs.setdefault((word, maxima), {"largest_actual": 0, "occurrences": 0, "depth": len(levels)})
            rec["largest_actual"] = max(rec["largest_actual"], len(S)); rec["occurrences"] += 1
        if count % 200 == 0:
            print(json.dumps({"colorings": count, "signatures": len(sigs), "seconds": round(time.time() - started)}), file=sys.stderr, flush=True)

    def extremal_value(p, cup_limit, cap_limit):
        for m in range(T, p - 1, -1):
            if data.get(m) is None:
                continue
            cups, caps, strong = data[m]
            base_ok = strong <= k - 1
            for comp in compositions(m, p):
                run = np.repeat(np.arange(p), comp)
                lim_cup = np.triu(cup_limit[run][:, run]); lim_cap = np.triu(cap_limit[run][:, run])
                good = base_ok & (cups <= lim_cup[None]).all(axis=(1, 2)) & (caps <= lim_cap[None]).all(axis=(1, 2))
                if good.any():
                    return m
        return 0

    rows = []
    for (word, maxima), rec in sigs.items():
        p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
        E = extremal_value(p, cup_limit, cap_limit)
        rows.append({"word": ["S" if w == "S" else f"{w[0]}{'L' if w[1]=='lower' else 'U'}" for w in word],
                     "sibling_maxima": list(maxima), "depth": rec["depth"], "runs": p,
                     "cup_limit": cup_limit.tolist(), "cap_limit": cap_limit.tolist(),
                     "E": E, "largest_actual": rec["largest_actual"], "occurrences": rec["occurrences"]})
    tight = sum(r["E"] == r["largest_actual"] for r in rows)
    out = {"max_n": T, "cases": {args.case: {"threshold": T, "signatures": len(rows), "tight": tight,
                                            "extremal_colorings_used": len(extremal), "rows": rows}}, "seconds": round(time.time() - started)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps({"case": args.case, "extremal_used": len(extremal), "signatures": len(rows), "tight": tight, "seconds": round(time.time() - started)}), file=sys.stderr)


if __name__ == "__main__":
    main()
