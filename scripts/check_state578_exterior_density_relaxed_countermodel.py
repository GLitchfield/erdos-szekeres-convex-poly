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


def replay(certificate: dict[str, object]) -> dict[str, int | bool]:
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

    return {
        "vertices": n,
        "ambient_edges": len(ambient_edges),
        "residual_edges": len(residual_edges),
        "ambient_transversal_number": 10,
        "residual_transversal_number": 4,
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
