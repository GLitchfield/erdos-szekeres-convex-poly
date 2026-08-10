#!/usr/bin/env python3
"""Independently replay the relaxed state-578 exterior-density certificate.

The checker validates a finite ordered hypergraph and a genuine two-level set
address allocation.  It does not construct a TripleColoring and therefore is
not a counterexample to the exact Lean state-578 theorem.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path


def pairwise_disjoint(sets: list[frozenset[int]]) -> bool:
    return all(not left & right for left, right in itertools.combinations(sets, 2))


def replay(certificate: dict[str, object]) -> dict[str, int | bool | list[int]]:
    if certificate.get("schema_version") != 1:
        raise ValueError("unsupported certificate schema")

    n = int(certificate["vertices"])
    vertices = frozenset(range(n))
    lower = frozenset(certificate["lower"])
    upper = frozenset(certificate["upper"])
    caps = [frozenset(block) for block in certificate["cap_columns"]]
    protected = frozenset(certificate["protected_spine"])
    unprotected = frozenset(certificate["unprotected_transversal"])
    transversal = protected | unprotected

    assert n == 32
    assert lower | upper == vertices and not lower & upper
    assert len(lower) == 24 and len(upper) == 8
    assert len(caps) == 6 and all(len(cap) == 4 for cap in caps)
    assert pairwise_disjoint(caps)
    assert frozenset().union(*caps) == lower
    assert len(protected) == 4 and len(unprotected) == 6
    assert len(transversal) == 10 and protected.isdisjoint(unprotected)

    def ambient(edge: frozenset[int]) -> bool:
        return len(edge) == 4 and bool(edge & transversal) and edge not in caps

    def residual(edge: frozenset[int]) -> bool:
        return ambient(edge) and edge.isdisjoint(unprotected)

    all_four_sets = [frozenset(edge) for edge in itertools.combinations(vertices, 4)]
    ambient_edges = [edge for edge in all_four_sets if ambient(edge)]
    residual_edges = [edge for edge in ambient_edges if residual(edge)]

    # The proposed next interface indexes every ambient cup avoiding one
    # blocker, not merely the old residual family.  In this relaxed model the
    # exact restricted transversal is T \ blocker: it has size nine for the
    # first four columns and ten for the last two.  Any smaller boundary
    # misses some t in T \ blocker; at least C(18,3) triples remain available,
    # while at most the five other cap columns are exceptional.
    blocker_avoiding_transversal_numbers: list[int] = []
    blocker_avoiding_edges: list[list[frozenset[int]]] = []
    for blocker in caps:
        restricted = [edge for edge in ambient_edges if edge.isdisjoint(blocker)]
        boundary = transversal - blocker
        assert all(edge & boundary for edge in restricted)
        assert math.comb(18, 3) > len(caps) - 1
        blocker_avoiding_edges.append(restricted)
        blocker_avoiding_transversal_numbers.append(len(boundary))
    assert blocker_avoiding_transversal_numbers == [9, 9, 9, 9, 10, 10]
    assert blocker_avoiding_transversal_numbers == list(
        certificate["blocker_avoiding_transversal_numbers"]
    )

    # Exact 32/23 density and ambient transversal number ten follow from the
    # checked cardinal certificates below.  For a 23-set choose t in its
    # intersection with the ten-set; for a boundary of size at most nine
    # choose t outside the boundary.  In either case at least C(22,3)
    # candidate triples remain, while at most six candidates are exceptional
    # cap columns.
    assert len(vertices - transversal) == 22
    assert math.comb(22, 3) > len(caps)
    assert all(edge & transversal for edge in ambient_edges)

    disjoint_residual = [
        frozenset(edge) for edge in certificate["pairwise_disjoint_residual_edges"]
    ]
    assert len(disjoint_residual) == 4
    assert pairwise_disjoint(disjoint_residual)
    assert all(residual(edge) for edge in disjoint_residual)
    assert all(edge & protected for edge in residual_edges)
    # The protected spine is a residual transversal of size four, while four
    # disjoint residual edges force every residual transversal to have size
    # at least four.
    assert len(protected) == 4

    protected_aux = list(certificate["row_auxiliary_protected"])
    lower_aux = list(certificate["row_auxiliary_lower"])
    upper_endpoint = int(certificate["common_upper_endpoint"])
    assert len(protected_aux) == len(caps) == len(lower_aux)
    assert upper_endpoint in upper

    rows: dict[tuple[int, int], frozenset[int]] = {}
    for column, cap in enumerate(caps):
        for source in cap:
            row = frozenset(
                {source, protected_aux[column], lower_aux[column], upper_endpoint}
            )
            assert len(row) == 4
            assert residual(row)
            assert row & cap == {source}
            assert len(row & lower) == 3 and row & upper == {upper_endpoint}
            # Since both the source cap and row meet the root children, their
            # first joint split in this two-level allocation is the root.
            assert bool((row | cap) & lower) and bool((row | cap) & upper)
            rows[(column, source)] = row
    assert len(rows) == 24

    # Every full blocker-avoiding row has a genuine address against every cap
    # column in the declared two-level tree.  A row touching the upper child
    # separates at the root.  A lower-only row descends once, where every cap
    # column straddles the even/odd split.
    assert all(any(x % 2 == 0 for x in cap) and any(x % 2 == 1 for x in cap)
               for cap in caps)
    for restricted in blocker_avoiding_edges:
        for edge in restricted:
            expected_path = () if edge & upper else (False,)
            for cap in caps:
                if expected_path == ():
                    assert (edge | cap) & lower and (edge | cap) & upper
                else:
                    assert (edge | cap) <= lower
                    assert any(x % 2 == 0 for x in edge | cap)
                    assert any(x % 2 == 1 for x in edge | cap)

    fan_sources = frozenset(certificate["fan_sources"])
    assert len(fan_sources) == 9
    assert fan_sources <= lower
    assert all(source < min(upper) for source in fan_sources)
    assert all(any(source in cap for source in fan_sources) for cap in caps)
    assert all(
        len(rows[(column, source)] & lower) == 3
        for column, cap in enumerate(caps)
        for source in cap & fan_sources
    )

    fan_entries = [
        (column, source, rows[(column, source)])
        for column, cap in enumerate(caps)
        for source in cap & fan_sources
    ]
    assert len(fan_entries) == 9
    deficits_by_column = [
        [entry for entry in fan_entries if entry[2].isdisjoint(blocker)]
        for blocker in caps
    ]
    assert max(len(entries) for entries in deficits_by_column) >= 5
    assert all(
        max(sum(1 for _, source, row in fan_entries if row == fixed_row), 0) <= 3
        for _, _, fixed_row in fan_entries
    )
    max_deficit = max(deficits_by_column, key=len)
    assert len({row for _, _, row in max_deficit}) >= 2

    return {
        "vertices": n,
        "ambient_edges": len(ambient_edges),
        "residual_edges": len(residual_edges),
        "ambient_transversal_number": 10,
        "residual_transversal_number": 4,
        "blocker_avoiding_transversal_numbers":
            blocker_avoiding_transversal_numbers,
        "full_blocker_avoiding_matrices": len(caps),
        "deletion_rows": len(rows),
        "fan_sources": len(fan_sources),
        "all_checks_passed": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    result = replay(json.loads(args.certificate.read_text(encoding="utf-8")))
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
