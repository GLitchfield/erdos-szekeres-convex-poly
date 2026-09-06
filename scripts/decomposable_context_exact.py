#!/usr/bin/env python3
"""Exact extremal value E of arbitrary context signatures from a compiled class
(tools/decomp_enum/enum_avoid output), against the recursion F.  Used to diagnose
additivity violations: for a violating (context, split), report E and F of the parent
and of both children under the violating split."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_depth2_tables import limits_from_signature  # noqa: E402
from decomposable_recursive_formula import make_F, parse_word  # noqa: E402
from decomposable_run_extremal import compositions  # noqa: E402
from decomposable_additivity_test import child  # noqa: E402

MASKW = 9


def load_class(class_dir: Path, max_n: int):
    data = {}
    for m in range(1, max_n + 1):
        if m <= 2:
            t = np.triu(np.full((m, m), 2, dtype=np.int8)); np.fill_diagonal(t, 1)
            data[m] = (t[None], t[None].copy(), np.array([m], dtype=np.int8)); continue
        f = class_dir / f"class_{m}.bin"
        if not f.exists():
            data[m] = None; continue
        raw = np.fromfile(f, dtype=np.uint8)
        rec = MASKW * 8 + 2 * m * m + 4
        count = raw.size // rec
        if count == 0:
            data[m] = None; continue
        recs = raw.reshape(count, rec)
        cups = recs[:, MASKW * 8: MASKW * 8 + m * m].astype(np.int8).reshape(count, m, m)
        caps = recs[:, MASKW * 8 + m * m: MASKW * 8 + 2 * m * m].astype(np.int8).reshape(count, m, m)
        strong = recs[:, -4].astype(np.int8)
        data[m] = (cups, caps, strong)
    return data


def exact(data, a, u, k, word, maxima, max_n):
    p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
    for m in range(max_n, p - 1, -1):
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--class-dir", type=Path, required=True)
    parser.add_argument("--max-n", type=int, required=True)
    parser.add_argument("--violations", type=Path, required=True, help="additivity test output")
    parser.add_argument("--limit", type=int, default=3)
    args = parser.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    F = make_F(a, u, k)
    data = load_class(args.class_dir, args.max_n)
    print("class loaded", {m: (len(v[2]) if v else 0) for m, v in data.items()}, file=sys.stderr, flush=True)
    v = json.load(open(args.violations))["violations"]
    seen = set()
    for x in v:
        word = parse_word(x["word"]); maxima = tuple(x["maxima"])
        key = (word, maxima, tuple(x["L"]), tuple(x["U"]))
        if (word, maxima) in seen:
            continue
        seen.add((word, maxima))
        if len(seen) > args.limit:
            break
        E_parent = exact(data, a, u, k, word, maxima, args.max_n)
        print(json.dumps({"word": x["word"], "maxima": x["maxima"], "F_parent": x["F"], "E_parent": E_parent, "split_value_F": x["best_split"]}), flush=True)
        L = frozenset(x["L"]); U = frozenset(x["U"])
        for dp in range(1, k - 1):
            c = k - 1 - dp
            for orient in ("L lower", "L upper"):
                if orient == "L lower":
                    w1, m1 = child(word, maxima, L, "lower", dp); w2, m2 = child(word, maxima, U, "upper", c)
                else:
                    w1, m1 = child(word, maxima, L, "upper", c); w2, m2 = child(word, maxima, U, "lower", dp)
                f1, f2 = F(w1, m1), F(w2, m2)
                if f1 + f2 == x["best_split"] and f1 and f2:
                    e1 = exact(data, a, u, k, w1, m1, args.max_n); e2 = exact(data, a, u, k, w2, m2, args.max_n)
                    print(json.dumps({"split": orient, "d'": dp, "child_L": {"word": ["S" if w == "S" else f"{w[0]}{'L' if w[1]=='lower' else 'U'}" for w in w1], "maxima": list(m1), "F": f1, "E": e1},
                                      "child_U": {"word": ["S" if w == "S" else f"{w[0]}{'L' if w[1]=='lower' else 'U'}" for w in w2], "maxima": list(m2), "F": f2, "E": e2}}), flush=True)
                    break
            else:
                continue
            break


if __name__ == "__main__":
    main()
