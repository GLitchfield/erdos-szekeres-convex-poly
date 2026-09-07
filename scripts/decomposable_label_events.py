#!/usr/bin/env python3
"""Search event-based orderings of the dead letters against a backbone file.

Each single-run context is decomposed into loss events relative to the root limits
(u-1, a-1): for each level l (outermost first), the cup and cap limits computed with
levels >= l only drop by some amounts; an *extension* event is attributed to the level's
letter nearest to the run on the side that realizes the chain step (left or right), a
*join* event (the strong coupling k-1-max binding) has no position.  Events carry
(letter, level, side-of-child, side-of-run, distance, kind).  An ordering is a sort key
over these features; the rule's tuple is the sorted letters truncated to the dead
count.  Every ordering is scored by how many classes' tuples are feasible."""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_depth2_tables import limits_from_signature  # noqa: E402


def parse(wd):
    out, i = [], 0
    while i < len(wd):
        if wd[i] == "S":
            out.append("S"); i += 1
        else:
            out.append((int(wd[i]), "lower" if wd[i + 1] == "L" else "upper")); i += 2
    return tuple(out)


def events_of(word, maxima, a, u, k):
    """Loss events of a single-run context."""
    nlev = len(maxima)
    first = min(i for i, w in enumerate(word) if w == "S")
    last = max(i for i, w in enumerate(word) if w == "S")
    side_at = {w[0]: w[1] for w in word if w != "S"}
    pos = {}
    for i, w in enumerate(word):
        if w != "S":
            pos.setdefault(w[0], []).append(i)

    def parts(l0):
        w2 = tuple(w if w == "S" else (w[0] - l0 + 1, w[1]) for w in word if w == "S" or w[0] >= l0)
        m2 = tuple(maxima[l0 - 1:])
        p2, cu, ca = limits_from_signature(w2, m2, a, u, k)
        return int(cu[0][0]), int(ca[0][0])

    # extension counts per side per chain type, using only levels >= l0
    def chain(l0, grow):
        w2 = tuple(w if w == "S" else (w[0] - l0 + 1, w[1]) for w in word if w == "S" or w[0] >= l0)
        # left/right ext via the DP of limits_from_signature is internal; recompute simply:
        # chains: one letter per level of the growing side, positions outward
        first2 = min(i for i, w in enumerate(w2) if w == "S"); last2 = max(i for i, w in enumerate(w2) if w == "S")
        lv = sorted({w[0] for w in w2 if w != "S" and w[1] == grow})
        def best(dirn):
            # dirn = -1 left, +1 right; returns (count, list of used positions)
            bestc, bestp = 0, []
            for r in range(len(lv) + 1):
                for sub in itertools.combinations(lv, r):
                    end = first2 if dirn < 0 else last2
                    used = []
                    ok = True
                    for l in sub:
                        cand = [i for i, w in enumerate(w2) if w != "S" and w[0] == l and ((i < end) if dirn < 0 else (i > end))]
                        if not cand:
                            ok = False; break
                        i = max(cand) if dirn < 0 else min(cand)
                        used.append((l + l0 - 1, i)); end = i
                    if ok and len(used) > bestc:
                        bestc, bestp = len(used), used
            return bestc, bestp
        return best(-1), best(+1)

    events = []
    prev = (u - 1, a - 1)
    prev_ext = {"lower": (0, 0), "upper": (0, 0)}
    for l0 in range(nlev, 0, -1):
        cl, pl = parts(l0)
        dcup, dcap = max(0, prev[0] - cl), max(0, prev[1] - pl)
        side = side_at.get(l0, "lower")
        for grow, letter, loss in (("lower", "L", dcup), ("upper", "U", dcap)):
            (lc, lp), (rc, rp) = chain(l0, grow)
            dl, dr = max(0, lc - prev_ext[grow][0]), max(0, rc - prev_ext[grow][1])
            prev_ext[grow] = (lc, rc)
            n_ext = 0
            for cnt, used, runside in ((dl, lp, "left"), (dr, rp, "right")):
                for j in range(min(cnt, loss - n_ext)):
                    lev, i = used[-1 - j] if used else (l0, None)
                    dist = (first - i if i is not None and i < first else (i - last if i is not None else 0))
                    events.append({"letter": letter, "level": l0, "child": side, "runside": runside, "dist": dist, "kind": "ext",
                                   "pos": (i if i is not None else first)})
                    n_ext += 1
            for j in range(loss - n_ext):
                events.append({"letter": letter, "level": l0, "child": side, "runside": "none", "dist": 0, "kind": "join", "pos": first})
        prev = (cl, pl)
    return events


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("backbone", type=Path)
    ap.add_argument("--top", type=int, default=15)
    ap.add_argument("--nfeat", type=int, default=3)
    args = ap.parse_args()
    d = json.load(open(args.backbone))
    a, u, k = (int(x) for x in d["case"].split(","))
    m = k - 2
    classes = []
    for key, opts in d["feasible"].items():
        wd, cl, pl = key.split("|"); cl, pl = int(cl), int(pl)
        word = parse(wd)
        nlev = max([w[0] for w in word if w != "S"] or [0])
        found = None
        for mx in itertools.product(range(1, k - 1), repeat=nlev):
            p, cu, ca = limits_from_signature(word, mx, a, u, k)
            if p == 1 and (int(cu[0][0]), int(ca[0][0])) == (cl, pl):
                found = mx; break
        if found is None:
            continue
        ev = events_of(word, found, a, u, k)
        fx = max(0, m - (cl - 1) - (pl - 1))
        classes.append((key, opts, ev, fx))
    print(f"{len(classes)} classes; event-count vs dead-count mismatches:",
          sum(1 for _, _, ev, fx in classes if len(ev) < fx))
    feats = ["dist", "level", "kind", "runside", "child", "letter", "pos"]
    dirs = {"dist": [(-1, "far"), (1, "near")], "level": [(-1, "outer"), (1, "inner")],
            "kind": [({"ext": 0, "join": 1}, "ext-first"), ({"ext": 1, "join": 0}, "join-first")],
            "runside": [({"right": 0, "left": 1, "none": 2}, "right-first"), ({"left": 0, "right": 1, "none": 2}, "left-first"),
                        ({"none": 0, "right": 1, "left": 2}, "none-first-right"), ({"none": 0, "left": 1, "right": 2}, "none-first-left")],
            "child": [({"lower": 0, "upper": 1}, "lower-first"), ({"upper": 0, "lower": 1}, "upper-first")],
            "letter": [({"L": 0, "U": 1}, "L-first"), ({"U": 0, "L": 1}, "U-first")],
            "pos": [(1, "left-to-right"), (-1, "right-to-left")]}
    results = []
    for order in itertools.permutations(feats, args.nfeat):
        for choices in itertools.product(*[dirs[f] for f in order]):
            def keyf(e):
                out = []
                for f, (dv, _) in zip(order, choices):
                    v = e[f]
                    out.append(dv * v if isinstance(dv, int) else dv[v])
                return tuple(out)
            for absorb in ("head", "tail"):
                score = 0
                for key, opts, ev, fx in classes:
                    seq = "".join(e["letter"] for e in sorted(ev, key=keyf))
                    tup = (seq[-fx:] if absorb == "head" else seq[:fx]) if fx else ""
                    tup = tup + "L" * (fx - len(tup))
                    score += tup in opts
                results.append((score, [f"{f}:{nm}" for f, (_, nm) in zip(order, choices)], absorb))
    results.sort(key=lambda r: -r[0])
    for score, desc, absorb in results[:args.top]:
        print(score, desc, absorb)


if __name__ == "__main__":
    main()
