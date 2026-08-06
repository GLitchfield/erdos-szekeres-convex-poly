#!/usr/bin/env python3
"""Independently replay the frozen coarse ray-event matrix gate."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from check_allocated_span_pascal_demand import Replay, file_sha256


Tree = int | tuple["Tree", "Tree"]
LOWER_TREE: Tree = ((8, (2, 1)), ((4, 7), 10))
UPPER_TREE: Tree = (((0, 3), ((6, 9), 5)), 11)
TREE: Tree = (LOWER_TREE, UPPER_TREE)
FRONTIER = ((0, 4), (2, 5), (4, 6), (5, 7), (6, 10), (8, 11))
RANK = 3
STRONG_SIZE = 7

Key = tuple[str, int, int]


def vertices(tree: Tree) -> tuple[int, ...]:
    if isinstance(tree, int):
        return (tree,)
    return tuple(sorted(vertices(tree[0]) + vertices(tree[1])))


def coloring_bits(tree: Tree, machine: Replay) -> int:
    if isinstance(tree, int):
        return 0
    left, right = tree
    support = sum(1 << vertex for vertex in vertices(tree))
    lower = sum(1 << vertex for vertex in vertices(left))
    return coloring_bits(left, machine) | coloring_bits(right, machine) | machine.crossing(
        support, lower
    )


def key_json(key: Key) -> list[object]:
    return list(key)


def minimum_hitting_size(
    zeros: frozenset[Key], earlier: tuple[frozenset[Key], ...]
) -> int | None:
    targets = [present & zeros for present in earlier]
    if any(not target for target in targets):
        return None
    relevant = sorted(set().union(*targets)) if targets else []
    for size in range(len(targets) + 1):
        for chosen in itertools.combinations(relevant, size):
            chosen_set = set(chosen)
            if all(target & chosen_set for target in targets):
                return size
    return None


def analyze() -> dict[str, object]:
    machine = Replay(12, STRONG_SIZE)
    support = sum(1 << vertex for vertex in vertices(TREE))
    lower = sum(1 << vertex for vertex in vertices(LOWER_TREE))
    upper_vertices = vertices(UPPER_TREE)
    upper = sum(1 << vertex for vertex in upper_vertices)
    bits = coloring_bits(TREE, machine)
    local = machine.ranks(bits, upper)
    if local is None:
        raise AssertionError("frozen active child unexpectedly contains a strong seven")

    def direction(span: tuple[int, int]) -> str:
        return "past" if lower & (1 << span[0]) else "future"

    def active_chains(span: tuple[int, int]) -> tuple[tuple[int, int], ...]:
        left, right = span
        if lower & (1 << left):
            return tuple(
                (start, finish)
                for start, finish in itertools.combinations(upper_vertices, 2)
                if left < start and finish == right
            )
        return tuple(
            (start, finish)
            for start, finish in itertools.combinations(upper_vertices, 2)
            if start == left and finish < right
        )

    def complementary_depth(span: tuple[int, int], ray: str, mark: int) -> int:
        left, right = span
        values = []
        if ray == "future":
            for endpoint in upper_vertices:
                if mark < endpoint < right:
                    values.append(local[1, mark, endpoint])
        else:
            for endpoint in upper_vertices:
                if left < endpoint < mark:
                    values.append(local[1, endpoint, mark])
        return min(max(values, default=0), STRONG_SIZE - 2)

    keys = tuple(
        (ray, role, depth)
        for ray in ("past", "future")
        for role in range(2)
        for depth in range(6)
    )
    chain_rows = tuple(active_chains(span) for span in FRONTIER)
    supports = []
    presents = []
    absents = []
    for span, chains in zip(FRONTIER, chain_rows, strict=True):
        if not chains:
            raise AssertionError("missing independent active chain")
        ray = direction(span)
        support_keys = frozenset(
            (ray, role, complementary_depth(span, ray, mark))
            for chain in chains
            for role, mark in enumerate(chain)
        )
        selected = min(chains, key=lambda chain: (1 << chain[0]) + (1 << chain[1]))
        present = frozenset(
            (ray, role, complementary_depth(span, ray, mark))
            for role, mark in enumerate(selected)
        )
        pool = set(keys) - support_keys
        absent = frozenset(
            sorted(pool, key=lambda key: (key[0] != ray, key[1], key[2]))[:3]
        )
        supports.append(support_keys)
        presents.append(present)
        absents.append(absent)

    supports_t = tuple(supports)
    presents_t = tuple(presents)
    absents_t = tuple(absents)
    pair_rows = []
    failures = []
    hitting = []
    for later in range(6):
        tau = minimum_hitting_size(frozenset(keys) - supports_t[later], presents_t[:later])
        hitting.append(
            {
                "later_index": later,
                "later_span": list(FRONTIER[later]),
                "minimum_zero_column_hitting_size": tau,
                "absent_card": 3,
            }
        )
        for earlier in range(later):
            intersection = sorted(presents_t[earlier] & absents_t[later])
            row = {
                "earlier_index": earlier,
                "later_index": later,
                "intersection": [key_json(key) for key in intersection],
            }
            pair_rows.append(row)
            if not intersection:
                failures.append(row)

    def undirected(source: frozenset[Key]) -> frozenset[tuple[int, int]]:
        return frozenset((role, depth) for _, role, depth in source)

    universe12 = tuple((role, depth) for role in range(2) for depth in range(6))
    support12 = tuple(undirected(support) for support in supports_t)
    present12 = tuple(undirected(present) for present in presents_t)
    absent12 = tuple(
        frozenset(sorted(set(universe12) - support)[:3]) for support in support12
    )
    failures12 = [
        [earlier, later]
        for later in range(6)
        for earlier in range(later)
        if not present12[earlier] & absent12[later]
    ]
    return {
        "maximum_n": 12,
        "strong_size": 7,
        "rank": 3,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "frontier": [list(span) for span in FRONTIER],
        "key_count": len(keys),
        "active_chains": [[list(chain) for chain in chains] for chains in chain_rows],
        "incidence_supports": [
            [key_json(key) for key in sorted(support)] for support in supports_t
        ],
        "deterministic_present_sets": [
            [key_json(key) for key in sorted(present)] for present in presents_t
        ],
        "fixed_absent_sets": [
            [key_json(key) for key in sorted(absent)] for absent in absents_t
        ],
        "ordered_pair_intersections": pair_rows,
        "fixed_selection_skew": not failures,
        "first_fixed_failure": failures[0] if failures else None,
        "minimum_hitting_rows": hitting,
        "direction_forgetting_diagnostic": {
            "key_count": len(universe12),
            "present_cards": [len(present) for present in present12],
            "absent_cards": [len(absent) for absent in absent12],
            "fixed_selection_skew": not failures12,
            "first_fixed_failure": failures12[0] if failures12 else None,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported schema")
    repo = Path(__file__).resolve().parent.parent
    for source in manifest["sources"].values():
        path = repo / source["path"]
        if file_sha256(path) != source["sha256"]:
            raise AssertionError(f"source hash mismatch: {source['path']}")
    replay = analyze()
    if replay != manifest["frozen_n12_k7"]:
        raise AssertionError("independent coarse-event replay differs")
    print(
        "fixed_selection_skew=",
        replay["fixed_selection_skew"],
        "first_failure=",
        replay["first_fixed_failure"],
        "hitting=",
        [row["minimum_zero_column_hitting_size"] for row in replay["minimum_hitting_rows"]],
    )


if __name__ == "__main__":
    main()
