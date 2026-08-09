#!/usr/bin/env python3
"""Independently verify the relaxed state-578 incidence countermodel.

The certificate deliberately contains no coloring.  The checker validates
only the finite-set consequences claimed in the associated experiment:
six disjoint caps, 32/23 four-cup density, transversal number ten, a private
owner ledger, the 2+1+1 selected-cup profile, and collapse of the raw
deletion-indexed ledger to two cups.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def fail(message: str) -> None:
    raise SystemExit(message)


def four_sets(vertices: frozenset[int]) -> set[frozenset[int]]:
    return {frozenset(items) for items in itertools.combinations(vertices, 4)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())

    n = data["universe_size"]
    universe = frozenset(range(n))
    caps = tuple(frozenset(block) for block in data["caps"])
    if n != 32 or len(caps) != 6 or any(len(cap) != 4 for cap in caps):
        fail("expected six four-caps on a 32-vertex universe")
    if any(not cap <= universe for cap in caps):
        fail("cap outside universe")
    for first, second in itertools.combinations(caps, 2):
        if first & second:
            fail("caps are not pairwise disjoint")
    cap_support = frozenset().union(*caps)
    if len(cap_support) != 24 or len(universe - cap_support) != 8:
        fail("six-cap support does not have the required 24+8 split")

    core = frozenset(data["complete_four_cup_core"])
    if len(core) != 13 or not core <= universe:
        fail("complete cup core must contain 13 universe vertices")
    base_cups = four_sets(core)
    selected = tuple(frozenset(cup) for cup in data["selected_cups"])
    if len(selected) != 3 or any(len(cup) != 4 for cup in selected):
        fail("expected three selected four-cups")
    cup_family = base_cups | set(selected)

    # It suffices to enumerate deletions from the 13-point core: deleting
    # fewer than nine core vertices leaves even more than four core vertices.
    for delete_count in range(10):
        for deleted in itertools.combinations(core, delete_count):
            remaining = core - frozenset(deleted)
            if len(remaining) < 4:
                fail("nine deletions removed too much of the core")
            witness = frozenset(next(itertools.combinations(remaining, 4)))
            if witness not in base_cups:
                fail("32/23 density witness missing from complete core")

    # Every cup meets every cap in at most two vertices, as it must in the
    # actual coloring semantics.
    for cup in cup_family:
        for cap in caps:
            if len(cup & cap) > 2:
                fail(f"cup-cap intersection exceeds two: {sorted(cup & cap)}")

    selected_support = frozenset().union(*selected)
    if len(selected_support) != 12:
        fail("selected cups are not a disjoint 12-vertex packing")
    if any(first & second for first, second in itertools.combinations(selected, 2)):
        fail("selected cups are not pairwise disjoint")
    regenerated = caps[data["regenerated_cap_index"]]
    profile = sorted(len(regenerated & cup) for cup in selected)
    if profile != [1, 1, 2] or not regenerated <= selected_support:
        fail("regenerated cap does not have the required 2+1+1 profile")
    for index in data["external_cap_indices"]:
        if caps[index] & selected_support:
            fail("an external cap meets the selected cup support")

    transversal = frozenset(data["private_transversal"])
    if len(transversal) != 10 or not transversal <= selected_support:
        fail("private transversal is not a ten-subset of the cup support")
    if any(not (transversal & cup) for cup in cup_family):
        fail("claimed transversal misses a cup")
    # The complete 4-uniform hypergraph on 13 vertices needs ten points to
    # hit every edge.  Enumerate all smaller core subsets independently.
    for size in range(10):
        for candidate in itertools.combinations(core, size):
            chosen = frozenset(candidate)
            if all(chosen & cup for cup in base_cups):
                fail("found a transversal of the complete core below ten")

    private_cups = {
        int(owner): frozenset(cup)
        for owner, cup in data["private_cups"].items()
    }
    if set(private_cups) != set(transversal):
        fail("private cup owners do not equal the transversal")
    if len(set(private_cups.values())) != len(transversal):
        fail("private cups are not owner-injective")
    for owner, cup in private_cups.items():
        if cup not in cup_family or transversal & cup != {owner}:
            fail(f"invalid private cup for owner {owner}")
        if not (cup - selected_support):
            fail(f"private cup for owner {owner} has no exterior vertex")

    collapsed = data["collapsed_deletion_cups"]
    first = frozenset(collapsed["first"])
    second = frozenset(collapsed["second"])
    if first not in cup_family or second not in cup_family or first & second:
        fail("collapsed deletion cups are not disjoint members of the family")
    used = set()
    for vertex in cap_support:
        cup = second if vertex in first else first
        if vertex in cup:
            fail(f"collapsed ledger cup contains deletion index {vertex}")
        used.add(cup)
    if used != {first, second}:
        fail("raw deletion ledger did not collapse to exactly two cups")

    print(json.dumps({
        "valid": True,
        "universe_size": n,
        "cap_count": len(caps),
        "cap_support": len(cap_support),
        "remainder": len(universe - cap_support),
        "base_cup_count": len(base_cups),
        "cup_family_count": len(cup_family),
        "transversal_number": len(transversal),
        "private_cup_count": len(private_cups),
        "raw_deletion_distinct_cups": len(used),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
