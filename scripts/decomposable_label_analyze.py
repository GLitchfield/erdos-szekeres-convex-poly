#!/usr/bin/env python3
"""Fit the label sets of single-run contexts (from decomposable_label_rule_sat.py
--features word --output) as cylinder windows: strings agreeing with fixed letters on a
set P of positions, with #L(free) <= ell and #U(free) <= ups.  Reports how many sets
are cylinders, with how many fixed positions, and how the fixed letters relate to the
word (positions and sides of the external letters)."""
from __future__ import annotations

import argparse
import itertools
import json
from collections import Counter, defaultdict
from pathlib import Path


def cylinder(m, P, Q, ell, ups):
    out = set()
    for X in range(1 << m):
        ok = True
        for i in P:
            if ((X >> i) & 1) != Q[i]:
                ok = False
                break
        if not ok:
            continue
        free = [i for i in range(m) if i not in P]
        nL = sum((X >> i) & 1 for i in free)
        nU = len(free) - nL
        if nL <= ell and nU <= ups:
            out.add(X)
    return frozenset(out)


def fit(m, labels):
    target = frozenset(sum(1 << i for i, ch in enumerate(lab) if ch == "L") for lab in labels)
    best = None
    for f in range(m + 1):
        for P in itertools.combinations(range(m), f):
            for bits in itertools.product((0, 1), repeat=f):
                Q = dict(zip(P, bits))
                for ell in range(m - f + 1):
                    for ups in range(m - f + 1):
                        if cylinder(m, P, Q, ell, ups) == target:
                            desc = (P, tuple("L" if Q[i] else "U" for i in P), ell, ups)
                            return desc
    return None


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("files", nargs="+", type=Path)
    args = ap.parse_args()
    for f in args.files:
        d = json.load(open(f))
        a, u, k = (int(x) for x in d["case"].split(","))
        m = k - 2
        sets = d["label_sets"]
        total = cyl = 0
        by_fixed = Counter()
        rows = []
        for key, labels in sets.items():
            if not key.startswith("["):
                continue
            phi = json.loads(key)
            if phi[0] == "multi":
                continue
            n, cl, pl, word = phi
            wd = "".join("S" if w == "S" else f"{w[0]}{'L' if w[1] == 'lower' else 'U'}" for w in word)
            total += 1
            desc = fit(m, labels)
            if desc is not None:
                cyl += 1
                by_fixed[len(desc[0])] += 1
            rows.append((n, wd, cl, pl, len(labels), desc, labels))
        print(f"{f.name}: single-run classes {total}, cylinders {cyl}, fixed-position histogram {dict(by_fixed)}")
        rows.sort(key=lambda r: (-r[0], r[1], r[2], r[3]))
        shown = 0
        for n, wd, cl, pl, size, desc, labels in rows:
            if size == 0:
                continue
            print(f"  n={n} {wd:12} cl={cl} pl={pl} |L|={size} cyl={desc} {labels if size <= 4 else ''}")
            shown += 1
            if shown >= 45:
                break


if __name__ == "__main__":
    main()
