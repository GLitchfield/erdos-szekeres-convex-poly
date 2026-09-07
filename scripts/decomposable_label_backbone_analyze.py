#!/usr/bin/env python3
"""Analyze a dead-letter backbone (decomposable_label_rule_sat.py --backbone), note 0123 §7.

For every single-run class (word | cup limit | cap limit) the backbone lists the feasible
dead-letter tuples.  This script (1) scores the "outer level first" event order and simple
positional orders against them, (2) tests coarsenings of the class features by a necessary
condition: a rule that is a function of a feature needs the feasible sets of every group
with that feature to intersect, and (3) prints the exception classes.

  python3 scripts/decomposable_label_backbone_analyze.py data/derived/label-sets/tight/backbone-4,4,5-s5.json
"""
from __future__ import annotations

import argparse
import collections
import itertools
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_depth2_tables import limits_from_signature  # noqa: E402
from decomposable_label_events import events_of, parse  # noqa: E402


def load(path):
    d = json.load(open(path))
    a, u, k = (int(x) for x in d["case"].split(","))
    m = k - 2
    rows = []
    for key, opts in d["feasible"].items():
        wd, cl, pl = key.split("|")
        cl, pl = int(cl), int(pl)
        word = parse(wd)
        nlev = max([w[0] for w in word if w != "S"] or [0])
        found = None
        for mx in itertools.product(range(1, k - 1), repeat=nlev):
            p, cu, ca = limits_from_signature(word, mx, a, u, k)
            if p == 1 and (int(cu[0][0]), int(ca[0][0])) == (cl, pl):
                found = mx
                break
        ev = events_of(word, found, a, u, k) if found is not None else []
        fx = max(0, m - (cl - 1) - (pl - 1))
        first = min(i for i, w in enumerate(word) if w == "S")
        last = max(i for i, w in enumerate(word) if w == "S")
        letters = []
        for i, w in enumerate(word):
            if w == "S":
                continue
            letters.append({"pos": i, "level": w[0], "letter": "L" if w[1] == "lower" else "U",
                            "dist": first - i if i < first else i - last, "side": "left" if i < first else "right"})
        rows.append({"key": key, "wd": wd, "cl": cl, "pl": pl, "opts": opts, "ev": ev, "fx": fx, "mx": found, "letters": letters})
    return rows, (a, u, k)


def tuple_of(seq, fx, take):
    tup = (seq[-fx:] if take == "last" else seq[:fx]) if fx else ""
    return tup + "L" * (fx - len(tup))


def score_orders(rows):
    out = []
    orders = {
        "events: outer level first, then far": (lambda r: sorted(r["ev"], key=lambda e: (-e["level"], -e["dist"])), "letter"),
        "letters: far to near, tie left": (lambda r: sorted(r["letters"], key=lambda x: (-x["dist"], x["side"] != "left")), "letter"),
        "letters: near to far, tie right": (lambda r: sorted(r["letters"], key=lambda x: (x["dist"], x["side"] != "right")), "letter"),
        "letters: outer level first, then far": (lambda r: sorted(r["letters"], key=lambda x: (-x["level"], -x["dist"])), "letter"),
        "letters: left to right": (lambda r: sorted(r["letters"], key=lambda x: x["pos"]), "letter"),
    }
    for name, (sort, field) in orders.items():
        for take in ("first", "last"):
            ok = sum(tuple_of("".join(e[field] for e in sort(r)), r["fx"], take) in r["opts"] for r in rows)
            out.append((ok, name, take))
    out.sort(key=lambda t: -t[0])
    return out


def coarsenings(rows):
    def E(r, fields):
        return sorted(tuple(e[f] for f in fields) for e in r["ev"])
    tests = {
        "limits only (cl, pl)": lambda r: (r["cl"], r["pl"]),
        "events (letter, level, kind, dist, runside, child) + limits": lambda r: (r["cl"], r["pl"], E(r, ["letter", "level", "kind", "dist", "runside", "child"])),
        "events (letter, level, kind, dist) + limits": lambda r: (r["cl"], r["pl"], E(r, ["letter", "level", "kind", "dist"])),
        "events (letter, level, kind) + limits": lambda r: (r["cl"], r["pl"], E(r, ["letter", "level", "kind"])),
        "events (letter, level) + limits": lambda r: (r["cl"], r["pl"], E(r, ["letter", "level"])),
        "events (letter, pos, kind) + limits": lambda r: (r["cl"], r["pl"], E(r, ["letter", "pos", "kind"])),
        "word with levels erased + limits": lambda r: (r["cl"], r["pl"], "".join(c for c in r["wd"] if not c.isdigit())),
        "word + limits (the class itself)": lambda r: r["key"],
    }
    out = []
    for name, phi in tests.items():
        groups = collections.defaultdict(list)
        for r in rows:
            groups[json.dumps(phi(r), sort_keys=True, default=str)].append(r)
        bad = []
        for rs in groups.values():
            inter = set(rs[0]["opts"])
            for r in rs[1:]:
                inter &= set(r["opts"])
            if not inter:
                bad.append([(r["key"], r["opts"]) for r in rs[:4]])
        out.append((name, len(groups), len(bad), bad[:2]))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("backbone", type=Path)
    ap.add_argument("--exceptions", type=int, default=12, help="exception classes to print per dead-letter count")
    ap.add_argument("--output", type=Path, default=None)
    args = ap.parse_args()
    rows, auk = load(args.backbone)
    print(f"{args.backbone}: case {auk}, {len(rows)} classes")
    print("options histogram:", dict(sorted(collections.Counter(len(r["opts"]) for r in rows).items())))
    print("classes with more loss events than dead letters:", sum(1 for r in rows if len(r["ev"]) > r["fx"]))
    print("\norders (classes whose tuple is feasible):")
    for ok, name, take in score_orders(rows):
        print(f"  {ok:6d}  {name:42s} take {take}")
    print("\ncoarsenings (groups whose feasible sets do not intersect):")
    res = coarsenings(rows)
    for name, ngroups, nbad, ex in res:
        print(f"  {name:62s} groups={ngroups:5d} conflicting={nbad:4d}")
        for g in ex:
            print("      e.g.", g)
    rule = lambda r: tuple_of("".join(e["letter"] for e in sorted(r["ev"], key=lambda e: (-e["level"], -e["dist"]))), r["fx"], "last")
    print("\nexceptions of the outer-level-first order:")
    for fx in sorted({r["fx"] for r in rows}):
        ex = [r for r in rows if r["fx"] == fx and rule(r) not in r["opts"]]
        print(f"  {fx} dead letters: {len(ex)} exceptions")
        for r in ex[: args.exceptions]:
            print(f"    {r['key']:18s} maxima={r['mx']} rule={rule(r)} feasible={r['opts']} events={[(e['letter'], e['level'], e['kind'], e['dist']) for e in r['ev']]}")
    if args.output:
        args.output.write_text(json.dumps({"case": auk, "orders": score_orders(rows),
                                           "coarsenings": [{"feature": n, "groups": g, "conflicting": b} for n, g, b, _ in res]}, indent=1) + "\n")


if __name__ == "__main__":
    main()
