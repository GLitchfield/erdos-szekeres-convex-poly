#!/usr/bin/env python3
"""The depth-one closed form of Workstream B (experiment 0118, addendum 2), checked
against every entry of the run-structure tables.

A lower child L with p runs, outer flags b (a sibling vertex before the first run)
and e (one after the last), and coupling d (the sibling's longest cap):

  plain(a,u,k; b,e,d)   = T(a, 1 + min(u-1-b-e, k-1-max(b+e, d)), k)
      for p = 1, and for p >= 2 whenever b or e is set: every cup of L is bounded by the
      reduced cup parameter and by the strong coupling; the runs cost nothing extra.

  inside(a,u,k; d)      = max over c <= min(u-2, k-2-d), d' <= a-2, c + d' <= k-1 of
                          T(a, c+1, k) + T(d'+1, min(u-1, k-d), k)
      for p in {2, 3} with no outer flag (the sibling strictly inside): run 1 is a lower part
      with cups at most c (a cup of run 1 extended by one run-2 vertex and joined with the
      sibling's cap gives c + 1 + d <= k - 1), run 2 an upper part with caps at most d'
      (extended by run 1 on the left) and cups at most min(u-2, k-1-d), and the two parts are
      coupled by c + d' <= k - 1.

Upper children are the mirror image (a and u exchanged).  T = decomposableThreshold.
Entries equal to 0 in the tables are run structures that cannot exist (an over-extended
pair); the formula is only compared where the structure exists.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path


def T(a, u, k):
    if a <= 1 or u <= 1:
        return 0
    if a + u <= k + 3:
        return math.comb(a + u - 4, a - 2)
    return sum(math.comb(k - 2, j) for j in range(k - a, u - 1))


def plain(a, u, k, b, e, d):
    lim = min(u - 1 - b - e, k - 1 - max(b + e, d))
    return T(a, lim + 1, k) if lim >= 1 else (1 if lim >= 0 else 0)


def inside(a, u, k, d):
    best = 0
    for c in range(1, min(u - 2, k - 2 - d) + 1):
        for dp in range(1, a - 1):
            if c + dp > k - 1:
                continue
            best = max(best, T(a, c + 1, k) + T(dp + 1, min(u - 1, k - d), k))
    return best


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()
    matched = mismatched = skipped = 0
    for f in args.files:
        d = json.load(open(f))
        for case, t in d["cases"].items():
            a, u, k = (int(x) for x in case.split(","))
            for side, (aa, uu) in (("E_low", (a, u)), ("E_up", (u, a))):
                for key, val in t[side].items():
                    parts = dict(x.split("=") for x in key.split(","))
                    p = int(parts["p"]); b = int(parts.get("sU", parts.get("sL"))); e = int(parts.get("eU", parts.get("eL")))
                    coup = int(parts.get("d", parts.get("c")))
                    if val == 0:
                        skipped += 1
                        continue
                    if p == 1 or b or e:
                        pred = plain(aa, uu, k, b, e, coup)
                    elif p in (2, 3):
                        pred = inside(aa, uu, k, coup)
                    else:
                        skipped += 1
                        continue
                    if pred == val:
                        matched += 1
                    else:
                        mismatched += 1
                        print(f"MISMATCH ({aa},{uu},{k}) {'upper' if side == 'E_up' else 'lower'} p={p} outer=({b},{e}) coupling={coup}: E={val} formula={pred}")
    print(json.dumps({"matched": matched, "mismatched": mismatched, "skipped_nonexistent_or_p4": skipped}))
    return 1 if mismatched else 0


if __name__ == "__main__":
    sys.exit(main())
