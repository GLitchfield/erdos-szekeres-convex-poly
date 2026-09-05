#!/usr/bin/env python3
"""Workstream B, step 2: exact extremal tables of subtrees at depth two and
more, by full context signature.

For each extremal coloring T of a case (a,u,k) and each subtree S of each
decomposition tree of T at depth >= 2, the context of S is the sweep-order
word of T's vertices with every external vertex tagged by its level along
S's path (1 = parent's sibling, 2 = grandparent's sibling, ...) and the side
of S at that level, together with each level's sibling chain maximum (its
longest cap when S is lower there, longest cup when upper).  S itself
contributes only its runs (which gaps of the external sequence it occupies).
By experiment 0117 the constraints on S are computed from this signature
alone: a cup from run i to run j may have at most
  u - 1 - (left levels usable from run i) - (right levels usable from run j)
vertices (longest-chain rule over the levels where S is lower) and at most
k - 1 - ext_strong(i, j) (join rule); caps mirror; strong sets of S at most
k - 1.  E(signature) is the largest decomposable S' with the same runs
meeting these constraints (numpy brute force over the class through
--max-n).  The output lists every distinct signature with E, the largest
actual |S| seen with it, and the scalar guess T(a, min(u1, kappa), k) built
from the spanning-cup limits, so that the loss structure at depth two can be
read against experiment 0118's depth-one pattern.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from collections import defaultdict
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import enumerate_class, coloring_dict, strong_sizes, threshold  # noqa: E402
from decomposable_context_functions import subtrees, path_levels, chain_max  # noqa: E402
from decomposable_run_extremal import chain_table, compositions  # noqa: E402


def signature(chi, n, S, levels):
    """(word, per-level chain maxima).  word: tuple over T's vertices of 'S' or (level, side)."""
    tag = {}
    maxima = []
    for li, (side, sibling) in enumerate(levels, start=1):
        for x in sibling:
            tag[x] = (li, side)
        maxima.append(chain_max(chi, sibling, left=(side == "upper")))   # S lower -> sibling's cap; S upper -> sibling's cup
        # chain_max(left=True) is the longest cup; S upper at this level means the sibling is below: its longest cup matters
    word = tuple("S" if v in S else tag[v] for v in range(n))
    return word, tuple(maxima)


def limits_from_signature(word, maxima, a, u, k):
    """Run structure and the cup/cap limit matrices by (run_i, run_j)."""
    # external sequence with gaps: runs of S are maximal blocks of 'S'
    runs = []          # list of (start_ext_index) : number of external vertices before the run
    ext = []           # tagged external vertices in order
    count_ext = 0
    in_run = False
    for w in word:
        if w == "S":
            if not in_run:
                runs.append(count_ext); in_run = True
        else:
            ext.append(w); count_ext += 1; in_run = False
    p = len(runs)
    levels = sorted({w[0] for w in ext})
    side_at = {}
    for w in ext:
        side_at[w[0]] = w[1]
    positions = defaultdict(list)     # level -> external positions
    for pos, w in enumerate(ext):
        positions[w[0]].append(pos)

    def extension(run_first, run_last, grow_side):
        """(count, strong_ext) for a chain starting in run_first and ending in run_last."""
        # a run r sits after external positions < runs[r]; an external vertex at position x is
        # left of run r iff x < runs[r], right of it iff x >= runs[r]
        left_states = {("gap", runs[run_first]): 0}
        right_states = {("gap", runs[run_last]): 0}
        best_strong = 0
        for li in levels:
            if side_at[li] != grow_side:
                continue
            below = max(left_states.values()) + max(right_states.values())
            best_strong = max(best_strong, below + maxima[li - 1])
            new_left = dict(left_states)
            for end, c in left_states.items():
                bound = end[1] if end[0] == "gap" else end[1]
                for x in positions[li]:
                    if x < bound and c + 1 > new_left.get(("ext", x), -1):
                        new_left[("ext", x)] = c + 1
            new_right = dict(right_states)
            for end, c in right_states.items():
                bound = end[1] if end[0] == "gap" else end[1] + 1
                for x in positions[li]:
                    if x >= bound and c + 1 > new_right.get(("ext", x), -1):
                        new_right[("ext", x)] = c + 1
            left_states, right_states = new_left, new_right
        count = max(left_states.values()) + max(right_states.values())
        return count, max(best_strong, count)

    cup_limit = np.zeros((p, p), dtype=np.int8)
    cap_limit = np.zeros((p, p), dtype=np.int8)
    for i in range(p):
        for j in range(i, p):
            e, es = extension(i, j, "lower")
            cup_limit[i][j] = min(u - 1 - e, k - 1 - es)
            e, es = extension(i, j, "upper")
            cap_limit[i][j] = min(a - 1 - e, k - 1 - es)
    return p, cup_limit, cap_limit


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--cases", default="4,4,5;4,5,5;5,5,5")
    parser.add_argument("--min-depth", type=int, default=2)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = time.time()
    classes, tindex = enumerate_class(args.max_n, progress=False)
    data = {}
    for m in range(1, args.max_n + 1):
        idx = tindex[m]
        masks = sorted(classes[m])
        cups = np.zeros((len(masks), m, m), dtype=np.int8); caps = np.zeros((len(masks), m, m), dtype=np.int8)
        strong = np.zeros(len(masks), dtype=np.int8)
        for r, mask in enumerate(masks):
            if m < 3:
                t = np.triu(np.full((m, m), 2, dtype=np.int8)); np.fill_diagonal(t, 1)
                cups[r] = caps[r] = t; strong[r] = m; continue
            chi = coloring_dict(mask, m, idx)
            cups[r] = chain_table(chi, m, True); caps[r] = chain_table(chi, m, False); strong[r] = strong_sizes(chi, m)
        data[m] = (cups, caps, strong)
    print(f"class tables to n={args.max_n} ({time.time()-started:.0f}s)", file=sys.stderr, flush=True)

    def extremal(a, u, k, p, cup_limit, cap_limit):
        for m in range(args.max_n, p - 1, -1):
            cups, caps, strong = data[m]
            base_ok = strong <= k - 1
            if not base_ok.any():
                continue
            for comp in compositions(m, p):
                run = np.repeat(np.arange(p), comp)
                lim_cup = np.triu(cup_limit[run][:, run]); lim_cap = np.triu(cap_limit[run][:, run])
                good = base_ok & (cups <= lim_cup[None]).all(axis=(1, 2)) & (caps <= lim_cap[None]).all(axis=(1, 2))
                if good.any():
                    return m
        return 0

    result = {"max_n": args.max_n, "cases": {}}
    for case in args.cases.split(";"):
        a, u, k = (int(x) for x in case.split(","))
        T = threshold(a, u, k)
        if T > args.max_n:
            continue
        idx = tindex[T]
        sigs = {}
        for mask in classes[T]:
            chi = coloring_dict(mask, T, idx)
            cup_end = chain_table(chi, T, True).max(); cap_end = chain_table(chi, T, False).max()
            if cap_end >= a or cup_end >= u or strong_sizes(chi, T) >= k:
                continue
            seen = subtrees(chi, T, classes, tindex)
            for S in seen:
                if len(S) < 3 or len(S) == T:
                    continue
                levels = path_levels(seen, S)
                if len(levels) < args.min_depth:
                    continue
                word, maxima = signature(chi, T, S, levels)
                key = (word, maxima)
                rec = sigs.setdefault(key, {"largest_actual": 0, "occurrences": 0, "depth": len(levels)})
                rec["largest_actual"] = max(rec["largest_actual"], len(S)); rec["occurrences"] += 1
        rows = []
        for (word, maxima), rec in sigs.items():
            p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
            E = extremal(a, u, k, p, cup_limit, cap_limit)
            # scalar guess from the spanning limits: cups from the first run to the last, caps likewise
            u1 = int(cup_limit[0][p - 1]) + 1; a1 = int(cap_limit[0][p - 1]) + 1
            guess = threshold(min(a, a1), min(u, u1), k) if min(a1, u1) >= 2 else 1
            rows.append({"word": ["S" if w == "S" else f"{w[0]}{'L' if w[1]=='lower' else 'U'}" for w in word],
                         "sibling_maxima": list(maxima), "depth": rec["depth"], "runs": p,
                         "cup_limit": cup_limit.tolist(), "cap_limit": cap_limit.tolist(),
                         "E": E, "largest_actual": rec["largest_actual"], "occurrences": rec["occurrences"],
                         "scalar_guess": guess, "loss_vs_guess": guess - E})
        rows.sort(key=lambda r: (-r["loss_vs_guess"], -r["E"]))
        result["cases"][case] = {"threshold": T, "signatures": len(rows), "rows": rows}
        losses = defaultdict(int)
        for r in rows:
            losses[r["loss_vs_guess"]] += 1
        print(json.dumps({"case": case, "threshold": T, "signatures": len(rows), "loss_histogram": dict(sorted(losses.items())),
                          "seconds": round(time.time() - started, 1)}), file=sys.stderr, flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=1) + "\n")


if __name__ == "__main__":
    main()
