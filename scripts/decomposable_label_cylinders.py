#!/usr/bin/env python3
"""Tabulate the cylinders chosen by decomposable_label_rule_sat.py --cylinders (flags or
levels features): per single-run class (n, cl, pl, per-level flags) the fixed positions,
fixed letters and budgets, with summary statistics."""
from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("file", type=Path)
    ap.add_argument("--show", type=int, default=40)
    args = ap.parse_args()
    d = json.load(open(args.file))
    a, u, k = (int(x) for x in d["case"].split(","))
    m = k - 2
    cyl = d["cylinders"]
    sets = d["label_sets"]
    stats = Counter()
    rows = []
    for key, picks in cyl.items():
        phi = json.loads(key)
        n, cl, pl, per = phi[0], phi[1], phi[2], phi[3]
        labels = sets.get(key, [])
        if not labels:
            continue
        f = max(0, m - (cl - 1) - (pl - 1))
        stats["classes"] += 1
        if len(picks) > 1:
            stats["multiple_cylinders_chosen"] += 1
        P, Q = picks[0]
        # budgets recovered from the labels
        free = [i for i in range(m) if i not in P]
        nLs = [sum(1 for i in free if lab[i] == "L") for lab in labels]
        nUs = [len(free) - x for x in nLs]
        e2, u2 = max(nLs), max(nUs)
        stats["fixed=f"] += len(P) == f
        stats["fixed>f"] += len(P) > f
        stats["budgets_tight"] += (e2 == cl - 1 and u2 == pl - 1)
        stats["prefix_positions"] += list(P) == list(range(len(P)))
        rows.append((n, cl, pl, per, P, Q, e2, u2, len(labels)))
    print(json.dumps({"case": d["case"], "s": d["s"], "features": d["features"], **stats}))
    # per (cl, pl, flags) pattern: which (|P|, Q-letters, budgets) occur
    pattern = defaultdict(Counter)
    for n, cl, pl, per, P, Q, e2, u2, size in rows:
        flags = tuple((sd[0], int(bool(b)), int(bool(e))) for sd, b, e in per)
        pattern[(cl, pl, flags)][(len(P), Q, e2, u2)] += 1
    shown = 0
    for key in sorted(pattern, key=lambda t: (len(t[2]), t)):
        print(f"cl={key[0]} pl={key[1]} flags={key[2]} -> {dict(pattern[key])}")
        shown += 1
        if shown >= args.show:
            break


if __name__ == "__main__":
    main()
