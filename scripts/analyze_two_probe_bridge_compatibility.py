#!/usr/bin/env python3
"""Enumerate two probes carrying bridge certificates on one three-point frame.

This is a deterministic route-selection calculation, not a proof producer.
It enumerates all 2^10 colorings of five ordered vertices, retains the
one-change colorings, and tests all same-gap head/tail certificate pairs.
"""

from __future__ import annotations

import itertools
import json


TRIPLES = tuple(itertools.combinations(range(5), 3))
QUADS = tuple(itertools.combinations(range(5), 4))


def one_change(assignment):
    for quad in QUADS:
        sequence = tuple(assignment[triple] for triple in itertools.combinations(quad, 3))
        if sum(left != right for left, right in zip(sequence, sequence[1:])) > 1:
            return False
    return True


def bridge(assignment, frame, probe, kind):
    quad = tuple(sorted((*frame, probe)))
    sequence = tuple(assignment[triple] for triple in itertools.combinations(quad, 3))
    if kind == "head":
        return sequence[0] == sequence[1] == sequence[2]
    return sequence[1] == sequence[2] == sequence[3]


def is_strong_five(assignment):
    for quad in QUADS:
        sequence = tuple(assignment[triple] for triple in itertools.combinations(quad, 3))
        if sequence[0] != sequence[1] or sequence[2] != sequence[3]:
            return False
    return True


def relation(assignment, first, second):
    return assignment[first] == assignment[second]


def equality_components(forced_equal, ordered):
    parent = {triple: triple for triple in TRIPLES}

    def find(triple):
        while parent[triple] != triple:
            parent[triple] = parent[parent[triple]]
            triple = parent[triple]
        return triple

    for first, second in forced_equal:
        first_root, second_root = find(first), find(second)
        parent[second_root] = first_root
    components = {}
    for triple in TRIPLES:
        components.setdefault(find(triple), []).append(
            tuple(ordered[index] for index in triple)
        )
    return sorted(
        (sorted(component) for component in components.values() if len(component) > 1),
        key=str,
    )


def main() -> None:
    reports = []
    for gap in range(4):
        ordered = ["x", "y", "z"]
        ordered[gap:gap] = ["q0", "q1"]
        position = {label: index for index, label in enumerate(ordered)}
        frame = tuple(position[label] for label in ("x", "y", "z"))
        probes = (position["q0"], position["q1"])
        for first_kind, second_kind in itertools.product(("head", "tail"), repeat=2):
            valid = []
            for bits in itertools.product((False, True), repeat=len(TRIPLES)):
                assignment = dict(zip(TRIPLES, bits))
                if not one_change(assignment):
                    continue
                if not bridge(assignment, frame, probes[0], first_kind):
                    continue
                if not bridge(assignment, frame, probes[1], second_kind):
                    continue
                valid.append(assignment)
            forced_equal = []
            forced_different = []
            for first, second in itertools.combinations(TRIPLES, 2):
                values = {relation(assignment, first, second) for assignment in valid}
                if values == {True}:
                    forced_equal.append((first, second))
                elif values == {False}:
                    forced_different.append((first, second))
            two_probe_triples = {
                triple for triple in TRIPLES if set(probes).issubset(triple)
            }
            forced_equal_touching_both_probes = [
                pair
                for pair in forced_equal
                if pair[0] in two_probe_triples or pair[1] in two_probe_triples
            ]
            reports.append({
                "gap": gap,
                "first_kind": first_kind,
                "second_kind": second_kind,
                "valid_colorings": len(valid),
                "strong_five_colorings": sum(is_strong_five(a) for a in valid),
                "forced_equal": forced_equal,
                "forced_equal_components": equality_components(forced_equal, ordered),
                "forced_equal_touching_both_probes":
                    forced_equal_touching_both_probes,
                "forced_different": forced_different,
            })
    print(json.dumps({"reports": reports}, sort_keys=True))


if __name__ == "__main__":
    main()
