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


def make_F(a, u, k):
    @lru_cache(maxsize=None)
    def F(word, maxima, cup_cap, cap_cap):
        p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
        cup_limit = np.minimum(cup_limit, cup_cap)
        cap_limit = np.minimum(cap_limit, cap_cap)
        if p == 1:
            cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
            if min(cl, pl) < 1:
                return 0
            return T(pl + 1, cl + 1, k) if min(cl, pl) >= 2 else 1
        best = 0
        for t in range(1, p):
            prefix = frozenset(range(t)); suffix = frozenset(range(t, p))
            for c in range(1, k):
                for dp in range(1, k):
                    if c + dp > k - 1:
                        continue
                    # orientation 1: prefix lower (cups <= c), suffix upper (caps <= dp)
                    w1, m1 = child_signature(word, maxima, prefix, "lower", dp)
                    w2, m2 = child_signature(word, maxima, suffix, "upper", c)
                    v1 = F(w1, m1, min(cup_cap, c), cap_cap)
                    v2 = F(w2, m2, cup_cap, min(cap_cap, dp)) if v1 else 0
                    if v1 and v2:
                        best = max(best, v1 + v2)
                    # orientation 2: prefix upper (caps <= dp), suffix lower (cups <= c)
                    w1, m1 = child_signature(word, maxima, prefix, "upper", c)
                    w2, m2 = child_signature(word, maxima, suffix, "lower", dp)
                    v1 = F(w1, m1, cup_cap, min(cap_cap, dp))
                    v2 = F(w2, m2, min(cup_cap, c), cap_cap) if v1 else 0
                    if v1 and v2:
                        best = max(best, v1 + v2)
        return best
    return F


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("tables", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    d = json.load(open(args.tables))
    result = {}
    for case, t in d["cases"].items():
        a, u, k = (int(x) for x in case.split(","))
        F = make_F(a, u, k)
        diffs = Counter()
        mism = []
        for r in t["rows"]:
            word = parse_word(r["word"]); maxima = tuple(r["sibling_maxima"])
            f = F(word, maxima, 99, 99)
            diffs[f - r["E"]] += 1
            if f != r["E"] and len(mism) < 40:
                mism.append({"word": "".join(r["word"]), "maxima": r["sibling_maxima"], "runs": r["runs"], "E": r["E"], "F": f,
                             "cup_limit": r["cup_limit"], "cap_limit": r["cap_limit"]})
        result[case] = {"threshold": t["threshold"], "signatures": len(t["rows"]), "F_minus_E": dict(sorted(diffs.items())), "mismatches": mism}
        print(json.dumps({"case": case, "signatures": len(t["rows"]), "F_minus_E": dict(sorted(diffs.items()))}), file=sys.stderr, flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=1) + "\n")


if __name__ == "__main__":
    main()
