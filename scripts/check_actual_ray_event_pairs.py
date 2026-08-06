#!/usr/bin/env python3
"""Produce the frozen gate for marked actual child-ray event pairs.

This implements the contrarian proposal literally: an event key contains a
normalized left/right ray direction, the complete child witness chain, and a
marked vertex of that chain.  The known cap/rank-three frontier has two-vertex
active child chains, so every selected present set has cardinality two.  The
gate records the first exact skew-Bollobas capacity obstruction.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from enumerate_allocated_span_pascal_demand import (
    DecomposableColorings,
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

Event = tuple[str, tuple[int, ...], int]


def event_json(event: Event) -> list[object]:
    direction, chain, mark = event
    return [direction, list(chain), mark]


def is_cap(
    colorings: DecomposableColorings, bits: int, chain: tuple[int, ...]
) -> bool:
    return all(
        colorings.color(bits, triple) == 0
        for triple in itertools.combinations(chain, 3)
    )


def frozen_record() -> dict[str, object]:
    colorings = DecomposableColorings(12)
    bits = tree_coloring_bits(FROZEN_TREE, colorings)
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    upper = support ^ lower
    upper_vertices = tuple(i for i in range(12) if upper & (1 << i))
    chain_size = RANK - 1
    chains = tuple(
        chain
        for chain in itertools.combinations(upper_vertices, chain_size)
        if is_cap(colorings, bits, chain)
    )
    universe: tuple[Event, ...] = tuple(
        (direction, chain, mark)
        for direction in ("left", "right")
        for chain in chains
        for mark in chain
    )

    def incident(span: tuple[int, int], event: Event) -> bool:
        left, right = span
        direction, chain, _ = event
        if lower & (1 << left):
            return direction == "left" and left < chain[0] and chain[-1] == right
        return direction == "right" and chain[0] == left and chain[-1] < right

    supports = tuple(
        frozenset(event for event in universe if incident(span, event))
        for span in FRONTIER
    )
    present_options = tuple(
        tuple(
            frozenset(
                (direction, chain, mark)
                for mark in chain
            )
            for direction, chain in sorted(
                {(event[0], event[1]) for event in support}
            )
        )
        for support in supports
    )
    if any(len(options) != 1 for options in present_options):
        raise AssertionError("frozen frontier no longer has unique active chains")
    selected = tuple(options[0] for options in present_options)
    if any(len(present) != chain_size for present in selected):
        raise AssertionError("marked witness does not have the required size")

    pair_difference = sorted(supports[1] - supports[2])
    if not pair_difference:
        raise AssertionError("cheapest adjacent support-difference gate failed")

    absent_card = STRONG_SIZE - RANK - 1
    first_obstruction = None
    for later in range(len(FRONTIER)):
        available = set(universe) - supports[later]
        prior = selected[:later]
        missing = [index for index, present in enumerate(prior) if not present & available]
        pairwise_disjoint = all(
            not prior[i] & prior[j]
            for i in range(len(prior))
            for j in range(i + 1, len(prior))
        )
        if missing or (pairwise_disjoint and len(prior) > absent_card):
            first_obstruction = {
                "later_index": later,
                "later_span": list(FRONTIER[later]),
                "prior_indices": list(range(later)),
                "prior_present_sets": [
                    [event_json(event) for event in sorted(present)]
                    for present in prior
                ],
                "all_prior_events_nonincident_later": not missing,
                "missing_prior_indices": missing,
                "prior_present_sets_pairwise_disjoint": pairwise_disjoint,
                "required_hits": len(prior) if pairwise_disjoint else None,
                "absent_card": absent_card,
            }
            break
    if first_obstruction is None:
        raise AssertionError("frozen frontier unexpectedly passed the event gate")

    return {
        "maximum_n": 12,
        "strong_size": STRONG_SIZE,
        "rank": RANK,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "upper_vertices": list(upper_vertices),
        "frontier": [list(span) for span in FRONTIER],
        "active_supports": [
            [event_json(event) for event in sorted(support)]
            for support in supports
        ],
        "unique_present_sets": [
            [event_json(event) for event in sorted(present)]
            for present in selected
        ],
        "adjacent_pair": {
            "earlier": list(FRONTIER[1]),
            "later": list(FRONTIER[2]),
            "support_difference": [event_json(event) for event in pair_difference],
            "passes": True,
        },
        "exact_size_skew_selection_exists": False,
        "first_obstruction": first_obstruction,
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_actual_ray_event_pairs.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-actual-ray-event-pair-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "event_key": (
                "normalized ray direction, complete exact-size active child "
                "chain, and one marked chain vertex"
            ),
            "present": "all marked events of one incident rank-1 child chain",
            "absent": (
                "k-rank-1 actual events not incident to the same span, chosen "
                "to meet every earlier present set"
            ),
            "claim_boundary": (
                "bounded refutation of this exact event key only; not a "
                "refutation of coarser ray events or full reflected candidates"
            ),
        },
        "frozen_n12_k7": frozen_record(),
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
