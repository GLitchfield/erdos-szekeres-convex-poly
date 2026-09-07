#!/usr/bin/env python3
"""Print the cylinders of single-run contexts (word features, --cylinders --single --prefix)
sorted by depth and word: fixed-letter prefix, budgets, size, limits."""
from __future__ import annotations
import argparse, json
from pathlib import Path

def fmt(word):
    return "".join("S" if w == "S" else f"{w[0]}{'L' if w[1] == 'lower' else 'U'}" for w in word)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file", type=Path)
    ap.add_argument("--max-levels", type=int, default=2)
    ap.add_argument("--min-n", type=int, default=1)
    ap.add_argument("--limit", type=int, default=80)
    args = ap.parse_args()
    d = json.load(open(args.file))
    a, u, k = (int(x) for x in d["case"].split(",")); m = k - 2
    cyl, sets = d["cylinders"], d["label_sets"]
    rows = []
    for key, picks in cyl.items():
        phi = json.loads(key); n, cl, pl, word = phi
        labels = sets.get(key, [])
        if not labels or not picks:
            continue
        P, Q = picks[0]
        free = [i for i in range(m) if i not in P]
        e2 = max(sum(1 for i in free if lab[i] == "L") for lab in labels)
        u2 = max(sum(1 for i in free if lab[i] == "U") for lab in labels)
        levels = max([w[0] for w in word if w != "S"] or [0])
        rows.append((levels, -n, fmt(word), n, cl, pl, Q, e2, u2, len(labels)))
    rows.sort()
    shown = 0
    for levels, negn, wd, n, cl, pl, Q, e2, u2, size in rows:
        if levels > args.max_levels or n < args.min_n:
            continue
        print(f"lv={levels} n={n} {wd:12} cl={cl} pl={pl}  fixed={Q!r:6} budgets=({e2},{u2}) |L|={size}")
        shown += 1
        if shown >= args.limit:
            break

if __name__ == "__main__":
    main()
