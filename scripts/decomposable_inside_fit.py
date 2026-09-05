#!/usr/bin/env python3
"""Invariant search for the sibling-inside value of Workstream B (experiment 0118):
E_in(a,u,k) = largest lower child with two runs, sibling strictly inside, coupling not
binding.  Candidates are signed sums of at most --terms shifted thresholds
T(a+da, u+du, k) with da, du in {0,-1,-2} and coefficients ±1; every candidate must match
every data point exactly.  Data points are read from run-extremal JSON files (E_low,
p=2, sU=0, eU=0, the smallest coupling d with k-d >= u)."""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import threshold  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+", type=Path)
    parser.add_argument("--terms", type=int, default=3)
    parser.add_argument("--max-shift", type=int, default=2)
    args = parser.parse_args()
    data = []
    for f in args.files:
        d = json.load(open(f))
        for case, t in d["cases"].items():
            a, u, k = (int(x) for x in case.split(","))
            # lower child: E_low at (a,u,k); upper child mirrors to a lower child at (u,a,k)
            for key, (aa, uu), chain_param in (("E_low", (a, u), u), ("E_up", (u, a), a)):
                for coup in range(1, k - 1):
                    if k - coup >= chain_param:
                        name = f"p=2,sU=0,eU=0,d={coup}" if key == "E_low" else f"p=2,sL=0,eL=0,c={coup}"
                        val = t[key].get(name)
                        if val:
                            point = ((aa, uu, k), val, threshold(aa, uu, k))
                            if point not in data:
                                data.append(point)
                        break
    print("data (case, E_in, T):", data)
    shifts = [(da, du) for da in range(0, -args.max_shift - 1, -1) for du in range(0, -args.max_shift - 1, -1)]
    survivors = []
    for nterms in range(1, args.terms + 1):
        for combo in itertools.combinations(shifts, nterms):
            for signs in itertools.product((1, -1, 2, -2), repeat=nterms):
                ok = True
                for (a, u, k), val, _ in data:
                    s = 0
                    for (da, du), sg in zip(combo, signs):
                        aa, uu = a + da, u + du
                        s += sg * (threshold(aa, uu, k) if aa >= 2 and uu >= 2 else (1 if aa >= 1 and uu >= 1 else 0))
                    if s != val:
                        ok = False
                        break
                if ok:
                    survivors.append((nterms, [(sg, da, du) for (da, du), sg in zip(combo, signs)]))
    print(f"{len(survivors)} candidate formulas match all {len(data)} points:")
    for nterms, terms in survivors[:30]:
        print("  E_in =", " ".join(f"{'+' if sg > 0 else '-'} T(a{da:+d},u{du:+d},k)" for sg, da, du in terms))


if __name__ == "__main__":
    main()
