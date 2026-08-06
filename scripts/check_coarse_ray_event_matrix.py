#!/usr/bin/env python3
"""Produce the frozen coarse actual-ray event incidence-matrix gate."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from enumerate_allocated_span_pascal_demand import (
    DecomposableColorings,
    LocalSpanAnalysis,
    file_sha256,
    git_revision,
    write_atomic,
)
from enumerate_reflected_transition_hall import (
    FROZEN_LOWER_TREE,
    FROZEN_TREE,
    tree_coloring_bits,
    tree_support,
)


FRONTIER = ((0, 4), (2, 5), (4, 6), (5, 7), (6, 10), (8, 11))
RANK = 3
STRONG_SIZE = 7
COLOR = 0

Key = tuple[str, int, int]


def key_json(key: Key) -> list[object]:
    return list(key)


def is_turn_set(
    colorings: DecomposableColorings,
    bits: int,
    chain: tuple[int, ...],
    color: int,
) -> bool:
    return all(
        colorings.color(bits, triple) == bool(color)
        for triple in itertools.combinations(chain, 3)
    )


def minimum_hitting_size(
    zero_keys: frozenset[Key], earlier: tuple[frozenset[Key], ...]
) -> int | None:
    targets = tuple(present & zero_keys for present in earlier)
    if any(not target for target in targets):
        return None
    relevant = sorted(set().union(*targets)) if targets else []
    for size in range(len(targets) + 1):
        if any(all(target & set(chosen) for target in targets)
               for chosen in itertools.combinations(relevant, size)):
            return size
    return None


def analyze() -> dict[str, object]:
    colorings = DecomposableColorings(12)
    bits = tree_coloring_bits(FROZEN_TREE, colorings)
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    upper = support ^ lower
    vertices = tuple(i for i in range(12) if support & (1 << i))
    active_vertices = tuple(i for i in vertices if upper & (1 << i))
    local = LocalSpanAnalysis(12, STRONG_SIZE).analyze(bits, upper)
    if local is None:
        raise AssertionError("frozen active child unexpectedly contains a strong seven")

    def direction(span: tuple[int, int]) -> str:
        return "past" if lower & (1 << span[0]) else "future"

    def active_chains(span: tuple[int, int]) -> tuple[tuple[int, ...], ...]:
        left, right = span
        if lower & (1 << left):
            return tuple(
                chain
                for chain in itertools.combinations(active_vertices, RANK - 1)
                if left < chain[0]
                and chain[-1] == right
                and is_turn_set(colorings, bits, chain, COLOR)
            )
        return tuple(
            chain
            for chain in itertools.combinations(active_vertices, RANK - 1)
            if chain[0] == left
            and chain[-1] < right
            and is_turn_set(colorings, bits, chain, COLOR)
        )

    def depth(span: tuple[int, int], ray_direction: str, mark: int) -> int:
        left, right = span
        if ray_direction == "future":
            ranks = [
                local[1 - COLOR, mark, endpoint]
                for endpoint in active_vertices
                if mark < endpoint < right
            ]
        else:
            ranks = [
                local[1 - COLOR, endpoint, mark]
                for endpoint in active_vertices
                if left < endpoint < mark
            ]
        return min(max(ranks, default=0), STRONG_SIZE - 2)

    all_keys: tuple[Key, ...] = tuple(
        (ray_direction, role, complementary_depth)
        for ray_direction in ("past", "future")
        for role in range(RANK - 1)
        for complementary_depth in range(STRONG_SIZE - 1)
    )
    chains_by_span = tuple(active_chains(span) for span in FRONTIER)
    if any(not chains for chains in chains_by_span):
        raise AssertionError("an active span has no exact-size witness chain")

    supports = []
    presents = []
    absents = []
    for span, chains in zip(FRONTIER, chains_by_span, strict=True):
        ray_direction = direction(span)
        support_keys = frozenset(
            (ray_direction, role, depth(span, ray_direction, mark))
            for chain in chains
            for role, mark in enumerate(chain)
        )
        selected_chain = min(chains, key=lambda chain: sum(1 << v for v in chain))
        present = frozenset(
            (ray_direction, role, depth(span, ray_direction, mark))
            for role, mark in enumerate(selected_chain)
        )
        absent_pool = set(all_keys) - support_keys
        ordered_pool = sorted(
            absent_pool,
            key=lambda key: (key[0] != ray_direction, key[1], key[2]),
        )
        absent = frozenset(ordered_pool[: STRONG_SIZE - RANK - 1])
        supports.append(support_keys)
        presents.append(present)
        absents.append(absent)

    supports_t = tuple(supports)
    presents_t = tuple(presents)
    absents_t = tuple(absents)
    if any(len(present) != RANK - 1 for present in presents_t):
        raise AssertionError("coarse present roles collapsed")
    if any(len(absent) != STRONG_SIZE - RANK - 1 for absent in absents_t):
        raise AssertionError("coarse absent pool is too small")
    if any(present & absent for present, absent in zip(presents_t, absents_t, strict=True)):
        raise AssertionError("coarse present and absent sets intersect locally")

    ordered_pairs = []
    fixed_failures = []
    hitting_rows = []
    for later in range(len(FRONTIER)):
        zero_keys = frozenset(all_keys) - supports_t[later]
        tau = minimum_hitting_size(zero_keys, presents_t[:later])
        hitting_rows.append(
            {
                "later_index": later,
                "later_span": list(FRONTIER[later]),
                "minimum_zero_column_hitting_size": tau,
                "absent_card": STRONG_SIZE - RANK - 1,
            }
        )
        for earlier in range(later):
            intersection = sorted(presents_t[earlier] & absents_t[later])
            record = {
                "earlier_index": earlier,
                "later_index": later,
                "intersection": [key_json(key) for key in intersection],
            }
            ordered_pairs.append(record)
            if not intersection:
                fixed_failures.append(record)

    def forget_direction(keys: frozenset[Key]) -> frozenset[tuple[int, int]]:
        return frozenset((role, complementary_depth) for _, role, complementary_depth in keys)

    undirected_universe = tuple(
        (role, complementary_depth)
        for role in range(RANK - 1)
        for complementary_depth in range(STRONG_SIZE - 1)
    )
    undirected_supports = tuple(forget_direction(support) for support in supports_t)
    undirected_presents = tuple(forget_direction(present) for present in presents_t)
    undirected_absents = tuple(
        frozenset(
            sorted(set(undirected_universe) - support)[: STRONG_SIZE - RANK - 1]
        )
        for support in undirected_supports
    )
    undirected_failures = [
        [earlier, later]
        for later in range(len(FRONTIER))
        for earlier in range(later)
        if not undirected_presents[earlier] & undirected_absents[later]
    ]

    return {
        "maximum_n": 12,
        "strong_size": STRONG_SIZE,
        "rank": RANK,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "frontier": [list(span) for span in FRONTIER],
        "key_count": len(all_keys),
        "active_chains": [[list(chain) for chain in chains] for chains in chains_by_span],
        "incidence_supports": [
            [key_json(key) for key in sorted(support)] for support in supports_t
        ],
        "deterministic_present_sets": [
            [key_json(key) for key in sorted(present)] for present in presents_t
        ],
        "fixed_absent_sets": [
            [key_json(key) for key in sorted(absent)] for absent in absents_t
        ],
        "ordered_pair_intersections": ordered_pairs,
        "fixed_selection_skew": not fixed_failures,
        "first_fixed_failure": fixed_failures[0] if fixed_failures else None,
        "minimum_hitting_rows": hitting_rows,
        "direction_forgetting_diagnostic": {
            "key_count": len(undirected_universe),
            "present_cards": [len(present) for present in undirected_presents],
            "absent_cards": [len(absent) for absent in undirected_absents],
            "fixed_selection_skew": not undirected_failures,
            "first_fixed_failure": undirected_failures[0] if undirected_failures else None,
        },
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_coarse_ray_event_matrix.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-coarse-ray-event-incidence-matrix-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "key": (
                "normalized active direction, ordinal role in an exact-size "
                "active chain, and clipped complementary one-sided ray depth"
            ),
            "present": "roles in the minimum binary-code active witness chain",
            "absence": "fiberwise nonincidence in the complete coarse support",
            "fixed_absent": (
                "first k-rank-1 absent keys ordered by direction match, role, depth"
            ),
            "claim_boundary": "bounded frozen-root gate only",
        },
        "frozen_n12_k7": analyze(),
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "base_producer": {
                "path": "scripts/enumerate_allocated_span_pascal_demand.py",
                "sha256": file_sha256(
                    repo / "scripts/enumerate_allocated_span_pascal_demand.py"
                ),
            },
            "base_checker": {
                "path": "scripts/check_allocated_span_pascal_demand.py",
                "sha256": file_sha256(
                    repo / "scripts/check_allocated_span_pascal_demand.py"
                ),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    write_atomic(args.output, produce(repo))
    print(args.output)


if __name__ == "__main__":
    main()
