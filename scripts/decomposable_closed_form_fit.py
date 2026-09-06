#!/usr/bin/env python3
"""Item 2 of the 6 September plan: does the depth-one child bound have a closed form in
shifted thresholds?  For each depth-one state class (runs p, outer flags, coupling d) the
value E(a,u,k) over all cases is fitted by signed sums of at most --terms terms
T(a+da, u+du, k+dk), da, du, dk in {0..-shift}, coefficients ±1, ±2, over the cases where
the structure exists.  Reports, per state, how many formulas match all its points (0 =
no closed form of this shape; the state's value is the recursion's maximum itself)."""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import threshold  # noqa: E402


def T(a, u, k):
    if a < 1 or u < 1 or k < 3:
        return 0
    if a < 2 or u < 2:
        return 1
    try:
        return threshold(a, u, k)
    except ValueError:
        return 0


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--terms", type=int, default=3)
    parser.add_argument("--shift", type=int, default=2)
    args = parser.parse_args()
    points = defaultdict(list)     # state -> [((a,u,k), E)]
    for f in args.files:
        d = json.load(open(f))
        for case, t in d["cases"].items():
            a, u, k = (int(x) for x in case.split(","))
            for side, (aa, uu) in (("E_low", (a, u)), ("E_up", (u, a))):
                for name, val in t[side].items():
                    parts = dict(x.split("=") for x in name.split(","))
                    p = int(parts["p"]); b = int(parts.get("sU", parts.get("sL"))); e = int(parts.get("eU", parts.get("eL")))
                    coup = int(parts.get("d", parts.get("c")))
                    if val == 0 or p > 3 or (p == 1 and not (b or e)):
                        continue
                    points[(p, b, e, coup)].append(((aa, uu, k), val))
    shifts = [(da, du, dk) for da in range(0, -args.shift - 1, -1) for du in range(0, -args.shift - 1, -1) for dk in range(0, -args.shift - 1, -1)]
    summary = {}
    for state, pts in sorted(points.items()):
        pts = sorted(set(pts))
        found = []
        for n in range(1, args.terms + 1):
            for combo in itertools.combinations(shifts, n):
                for signs in itertools.product((1, -1, 2, -2), repeat=n):
                    ok = True
                    for (a, u, k), val in pts:
                        s = sum(sg * T(a + da, u + du, k + dk) for (da, du, dk), sg in zip(combo, signs))
                        if s != val:
                            ok = False
                            break
                    if ok:
                        found.append(" ".join(f"{sg:+d}T(a{da:+d},u{du:+d},k{dk:+d})" for (da, du, dk), sg in zip(combo, signs)))
            if found:
                break
        summary[f"p={state[0]},before={state[1]},after={state[2]},coupling={state[3]}"] = {"points": len(pts), "formulas": len(found), "examples": found[:3]}
    for k2, v in summary.items():
        print(k2, v)


if __name__ == "__main__":
    main()
