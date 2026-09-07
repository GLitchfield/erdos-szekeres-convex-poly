#!/usr/bin/env python3
"""Workstream B, step 3 test: the depth-one formula applied recursively.

For a context signature (experiment 0119: the sweep word with external vertices
tagged by level and side, the per-level sibling chain maxima, and the child's
runs), define

  F(sig) = max( T(1 + cap_limit[0][p-1], 1 + cup_limit[0][p-1], k),        (one structure)
                max over cuts t, c, d' with c + d' <= k-1 of
                    F(prefix runs 0..t-1 as a lower part with the suffix as a new level-1 upper
                      sibling of longest cap d', own cups capped at c)
                  + F(suffix runs t..p-1 as an upper part with the prefix as a new level-1 lower
                      sibling of longest cup c, own caps capped at d') )

where the limit matrices come from the context rules of experiment 0117
(scripts/decomposable_depth2_tables.py).  At depth one this is exactly the
closed form of experiment 0118 (addendum 2).  The script evaluates F on every
signature of the depth-two tables and compares it with the exact E: F < E means
the stacked cuts miss a structure, F > E means the recursion is not a valid
bound, F = E everywhere means the recursion is the induction hypothesis.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import threshold  # noqa: E402
from decomposable_depth2_tables import limits_from_signature  # noqa: E402


def T(a, u, k):
    if a <= 1 or u <= 1:
        return 0
    return threshold(a, u, k)


def parse_word(word):
    out = []
    for w in word:
        if w == "S":
            out.append("S")
        else:
            out.append((int(w[:-1]), "lower" if w[-1] == "L" else "upper"))
    return tuple(out)


def run_index(word):
    """run number of each S position (None for external)."""
    idx = []
    r = -1
    prev_s = False
    for w in word:
        if w == "S":
            if not prev_s:
                r += 1
            idx.append(r)
            prev_s = True
        else:
            idx.append(None)
            prev_s = False
    return idx


def child_signature(word, maxima, keep_runs, side_of_child, sibling_max):
    """Signature of the part made of ``keep_runs``: the other runs' vertices become a new
    level-1 sibling (the child is ``side_of_child`` there), old levels shift by one."""
    ridx = run_index(word)
    new_word = []
    for w, r in zip(word, ridx):
        if w == "S":
            new_word.append("S" if r in keep_runs else (1, side_of_child))
        else:
            new_word.append((w[0] + 1, w[1]))
    return tuple(new_word), (sibling_max,) + tuple(maxima)


CACHE_SIZE = None   # None = unbounded; a shard driver sets e.g. 3_000_000 to bound memory


def make_F2(a, u, k, *, include_zero_children=False):
    """Interval-cut recursion: like F, but a cut may take any contiguous block of the child's
    letters as one part (a sandwich when the block is interior), with the rest as the other
    part; both orientations and all couplings.  Single runs are the base case as in F.

    The historical F2 drops a cut when either child has value zero.  Set
    include_zero_children=True for the sum used by Ctx.Context.boundFuel in Lean,
    including its full level domain and natural-number limit arithmetic.
    Keeping the historical default preserves the meaning of existing F2 experiments.
    """
    from decomposable_additivity_test import child as child_letters

    @lru_cache(maxsize=CACHE_SIZE)
    def F2(word, maxima):
        p, cup_limit, cap_limit = limits_from_signature(
            word, maxima, a, u, k, lean=include_zero_children)
        s_pos = [i for i, w in enumerate(word) if w == "S"]
        if p == 1 and len(s_pos) == 1:
            cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
            if min(cl, pl) < 1:
                return 0
            return T(pl + 1, cl + 1, k) if min(cl, pl) >= 2 else 1
        if p == 1:
            # a single run is the base case (the Lean `bound` convention): the classical
            # threshold with the run's internal parameters, no cuts inside the run
            cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
            if min(cl, pl) < 1:
                return 0
            return T(pl + 1, cl + 1, k) if min(cl, pl) >= 2 else 1
        best = 0
        n = len(s_pos)
        for i in range(n):
            for j in range(i, n):
                if i == 0 and j == n - 1:
                    continue
                block = frozenset(s_pos[i:j + 1]); rest = frozenset(s_pos) - block
                for dp in range(1, k - 1):
                    c = k - 1 - dp
                    for (side_b, side_r) in (("lower", "upper"), ("upper", "lower")):
                        wb, mb = child_letters(word, maxima, block, side_b, dp if side_b == "lower" else c)
                        vb = F2(wb, mb)
                        if not include_zero_children and not vb:
                            continue
                        wr, mr = child_letters(word, maxima, rest, side_r, c if side_r == "upper" else dp)
                        vr = F2(wr, mr)
                        if include_zero_children or vr:
                            best = max(best, vb + vr)
        return best
    return F2


def make_F(a, u, k):
    """F(word, maxima): the coupling of a cut is carried entirely by the two new sibling maxima,
    d' for the prefix's view of the suffix and k-1-d' for the suffix's view of the prefix; the
    join rule of experiment 0117 then bounds every chain of each part (an explicit cap on a
    part's own chains would have to shrink under the part's own later cuts, and is redundant
    once the cup bound of the lower part is k-1-d')."""
    @lru_cache(maxsize=None)
    def F(word, maxima):
        p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
        if p == 1:
            cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
            if min(cl, pl) < 1:
                return 0
            return T(pl + 1, cl + 1, k) if min(cl, pl) >= 2 else 1
        best = 0
        for t in range(1, p):
            prefix = frozenset(range(t)); suffix = frozenset(range(t, p))
            for dp in range(1, k - 1):
                c = k - 1 - dp
                # orientation 1: prefix lower (sees the suffix's longest cap d'), suffix upper (sees cup c)
                w1, m1 = child_signature(word, maxima, prefix, "lower", dp)
                v1 = F(w1, m1)
                if v1:
                    w2, m2 = child_signature(word, maxima, suffix, "upper", c)
                    v2 = F(w2, m2)
                    if v2:
                        best = max(best, v1 + v2)
                # orientation 2: prefix upper (sees the suffix's longest cup c), suffix lower (sees cap d')
                w1, m1 = child_signature(word, maxima, prefix, "upper", c)
                v1 = F(w1, m1)
                if v1:
                    w2, m2 = child_signature(word, maxima, suffix, "lower", dp)
                    v2 = F(w2, m2)
                    if v2:
                        best = max(best, v1 + v2)
        return best
    return F


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("tables", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--recursion", choices=("F", "F2"), default="F")
    parser.add_argument("--shard", default=None, help="i/N: only every N-th row starting at i")
    parser.add_argument("--cache-size", type=int, default=None)
    parser.add_argument("--cases", default=None, help="semicolon-separated subset of cases, e.g. 5,5,5;4,5,5")
    parser.add_argument("--max-child", type=int, default=None, help="skip rows with more child letters than this")
    parser.add_argument("--min-child", type=int, default=None, help="skip rows with fewer child letters than this")
    parser.add_argument("--checkpoint", type=int, default=0,
                        help="write <output>.partial.json every N rows and resume from it if present (0 = off)")
    args = parser.parse_args()
    global CACHE_SIZE
    if args.cache_size:
        CACHE_SIZE = args.cache_size
    shard_i, shard_n = (int(x) for x in args.shard.split("/")) if args.shard else (0, 1)
    d = json.load(open(args.tables))
    result = {}
    partial_path = args.output.with_suffix(".partial.json")
    partial = {}
    if args.checkpoint and partial_path.exists():
        partial = json.loads(partial_path.read_text())
        print(json.dumps({"resume": str(partial_path), "cases": {c: v["done"] for c, v in partial.items()}}), file=sys.stderr, flush=True)
    for case, t in d["cases"].items():
        if args.cases and case not in args.cases.split(";"):
            continue
        a, u, k = (int(x) for x in case.split(","))
        F = make_F2(a, u, k) if args.recursion == "F2" else make_F(a, u, k)
        diffs = Counter()
        mism = []
        done = 0
        if case in partial:
            # the rows are processed in order, so a checkpoint is a prefix of this shard's rows
            diffs = Counter({int(x): n for x, n in partial[case]["F_minus_E"].items()})
            mism = partial[case]["mismatches"]
            done = partial[case]["done"]
        processed = 0
        rows = [r for r in t["rows"]
                if (args.max_child is None or sum(1 for w in r["word"] if w == "S") <= args.max_child)
                and (args.min_child is None or sum(1 for w in r["word"] if w == "S") >= args.min_child)]
        for row_index, r in enumerate(rows):
            if row_index % shard_n != shard_i:
                continue
            processed += 1
            if processed <= done:
                continue
            word = parse_word(r["word"]); maxima = tuple(r["sibling_maxima"])
            f = F(word, maxima)
            diffs[f - r["E"]] += 1
            if f != r["E"] and len(mism) < 40:
                mism.append({"word": "".join(r["word"]), "maxima": r["sibling_maxima"], "runs": r["runs"], "E": r["E"], "F": f,
                             "cup_limit": r["cup_limit"], "cap_limit": r["cap_limit"]})
            if args.checkpoint and processed % args.checkpoint == 0:
                partial[case] = {"done": processed, "F_minus_E": dict(sorted(diffs.items())), "mismatches": mism}
                partial_path.parent.mkdir(parents=True, exist_ok=True)
                tmp = partial_path.with_suffix(".tmp")
                tmp.write_text(json.dumps(partial) + "\n")
                tmp.replace(partial_path)
                print(json.dumps({"case": case, "checkpoint": processed, "F_minus_E": dict(sorted(diffs.items()))}), file=sys.stderr, flush=True)
        result[case] = {"threshold": t["threshold"], "signatures": sum(diffs.values()), "F_minus_E": dict(sorted(diffs.items())), "mismatches": mism,
                        "recursion": args.recursion, "shard": args.shard, "skipped_rows": len(t["rows"]) - len(rows),
                        "max_child": args.max_child, "min_child": args.min_child}
        partial[case] = {"done": processed, "F_minus_E": dict(sorted(diffs.items())), "mismatches": mism}
        print(json.dumps({"case": case, "signatures": sum(diffs.values()), "recursion": args.recursion, "shard": args.shard, "F_minus_E": dict(sorted(diffs.items()))}), file=sys.stderr, flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=1) + "\n")
    if args.checkpoint and partial_path.exists():
        partial_path.unlink()


if __name__ == "__main__":
    main()
