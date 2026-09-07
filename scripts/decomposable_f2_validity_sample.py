#!/usr/bin/env python3
"""Validity of the recursions on real subtrees at k = 6: sample extremal colorings of a
compiled class, build one decomposition tree of each, and for every subtree S with its
context signature check |S| <= F2(signature) (interval cuts) and record where the stacked
F falls below |S|.  Any |S| > F2 disproves F2 as an induction hypothesis."""
from __future__ import annotations

import argparse
import itertools
import json
import random
import sys
import time
from functools import lru_cache
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_recursive_formula import make_F, make_F2  # noqa: E402
from decomposable_depth2_tables import signature  # noqa: E402
from decomposable_context_functions import chain_max  # noqa: E402

MASKW = 9


def decode(mask_words, n):
    mask = 0
    for i, w in enumerate(mask_words):
        mask |= int(w) << (64 * i)
    chi = {}
    for t, tri in enumerate(itertools.combinations(range(n), 3)):
        chi[tri] = bool(mask >> t & 1)
    return chi


def one_tree(chi, vertices):
    """One decomposition tree: {node: (parent, side)} with the root mapped to None."""
    vertices = tuple(vertices)
    seen = {vertices: None}

    @lru_cache(maxsize=None)
    def decomposable(vs):
        if len(vs) == 1:
            return True
        for lower_bits in range(1, (1 << len(vs)) - 1):
            lower = tuple(v for i, v in enumerate(vs) if lower_bits >> i & 1)
            upper = tuple(v for i, v in enumerate(vs) if not lower_bits >> i & 1)
            ok = True
            for i, j, k in itertools.combinations(vs, 3):
                inl = (i in lower) + (j in lower) + (k in lower)
                if 0 < inl < 3 and chi[(i, j, k)] != (j in lower):
                    ok = False
                    break
            if ok and decomposable(lower) and decomposable(upper):
                return (lower, upper)
        return False

    stack = [vertices]
    while stack:
        vs = stack.pop()
        if len(vs) == 1:
            continue
        split = decomposable(vs)
        if not split:
            return None
        lower, upper = split
        seen[lower] = (vs, "lower"); seen[upper] = (vs, "upper")
        stack.extend([lower, upper])
    return seen


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--class-file", type=Path, required=True)
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--samples", type=int, default=40)
    parser.add_argument("--seed", type=int, default=20260906)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    n = args.n
    F = make_F(a, u, k); F2 = make_F2(a, u, k)
    raw = np.memmap(args.class_file, dtype=np.uint8, mode="r")
    rec = MASKW * 8 + 2 * n * n + 4
    count = raw.size // rec
    rng = random.Random(args.seed)
    picks = sorted(rng.sample(range(count), min(args.samples, count)))
    started = time.time()
    stats = {"colorings": 0, "subtrees": 0, "F2_below_size": 0, "F_below_size": 0, "F_below_F2": 0}
    bad = []
    for idx in picks:
        words = np.array(raw[idx * rec: idx * rec + MASKW * 8]).view(np.uint64)
        chi = decode(words, n)
        print(json.dumps({"sample": idx, "status": "tree search", "seconds": round(time.time() - started)}), file=sys.stderr, flush=True)
        tree = one_tree(chi, range(n))
        if tree is None:
            continue
        stats["colorings"] += 1
        for S, parent in tree.items():
            if parent is None or len(S) < 2:
                continue
            levels = []
            node = S
            while tree[node] is not None:
                par, side = tree[node]
                levels.append((side, tuple(v for v in par if v not in node)))
                node = par
            word, maxima = signature(chi, n, S, levels)
            f, f2 = F(word, maxima), F2(word, maxima)
            stats["subtrees"] += 1
            if f2 < len(S):
                stats["F2_below_size"] += 1
                if len(bad) < 20:
                    bad.append({"size": len(S), "F2": f2, "F": f, "word": ["S" if w == "S" else f"{w[0]}{'L' if w[1]=='lower' else 'U'}" for w in word], "maxima": list(maxima)})
            if f < len(S):
                stats["F_below_size"] += 1
            if f < f2:
                stats["F_below_F2"] += 1
        print(json.dumps({**stats, "seconds": round(time.time() - started)}), file=sys.stderr, flush=True)
    out = {"case": args.case, "n": n, "samples": len(picks), "stats": stats, "F2_below_size_examples": bad, "seconds": round(time.time() - started)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
