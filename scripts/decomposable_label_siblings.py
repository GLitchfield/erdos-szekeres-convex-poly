#!/usr/bin/env python3
"""For a cylinder label-set solution (decomposable_label_rule_sat.py --cylinders --single
--features word --output), print for the root's partitions the two parts' contexts, their
limits and their cylinders side by side, to read how the coupling and the letter positions
determine the fixed letters."""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_depth2_tables import limits_from_signature  # noqa: E402
from decomposable_additivity_test import child as child_letters  # noqa: E402


def fmt(word):
    return "".join("S" if w == "S" else f"{w[0]}{'L' if w[1] == 'lower' else 'U'}" for w in word)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("file", type=Path)
    ap.add_argument("--max-rows", type=int, default=60)
    ap.add_argument("--interval-only", action="store_true")
    args = ap.parse_args()
    d = json.load(open(args.file))
    a, u, k = (int(x) for x in d["case"].split(","))
    m = k - 2
    cyl = d["cylinders"]
    sets = d["label_sets"]

    def info(word, maxima):
        p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
        if p != 1:
            return None
        cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
        n = sum(1 for w in word if w == "S")
        key = json.dumps([n, cl, pl, list(word)], default=str)
        # keys were dumped with json.dumps(phi, default=str) where word is a tuple of str/tuples
        key = json.dumps((n, cl, pl, word), default=str)
        picks = cyl.get(key)
        labels = sets.get(key, [])
        if picks is None:
            return (cl, pl, None, labels)
        P, Q = picks[0] if picks else ((), "")
        free = [i for i in range(m) if i not in P]
        e2 = max([sum(1 for i in free if lab[i] == "L") for lab in labels] or [0])
        u2 = max([sum(1 for i in free if lab[i] == "U") for lab in labels] or [0])
        return (cl, pl, (len(P), Q, e2, u2), labels)

    s = d["s"]
    word = tuple(["S"] * s)
    maxima = tuple()
    s_pos = list(range(s))
    shown = 0
    for r in range(1, s):
        for keep in itertools.combinations(s_pos, r):
            A = frozenset(keep)
            R = frozenset(s_pos) - A
            if args.interval_only and (max(keep) - min(keep) + 1 != len(keep)):
                continue
            for dp in range(1, k - 1):
                c = k - 1 - dp
                wa, ma = child_letters(word, maxima, A, "lower", dp)
                wr, mr = child_letters(word, maxima, R, "upper", c)
                ia, ir = info(wa, ma), info(wr, mr)
                if ia is None or ir is None:
                    continue
                if not ia[3] or not ir[3]:
                    continue
                print(f"d={dp}: A={fmt(wa):12} cl,pl=({ia[0]},{ia[1]}) cyl={ia[2]} {ia[3] if len(ia[3]) <= 3 else len(ia[3])}   |   "
                      f"R={fmt(wr):12} cl,pl=({ir[0]},{ir[1]}) cyl={ir[2]} {ir[3] if len(ir[3]) <= 3 else len(ir[3])}")
                shown += 1
                if shown >= args.max_rows:
                    return


if __name__ == "__main__":
    main()
