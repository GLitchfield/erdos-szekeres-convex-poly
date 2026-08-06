#!/usr/bin/env python3
"""Produce a bounded counterexample to the active-representative shortcut.

The reflected candidate family passes Hall on this complete five-span block,
but the single candidate selected by the child-ray bridge alternates between
only two ideals.  This refutes deterministic representative injectivity, not
consecutive-block Hall.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from enumerate_allocated_span_pascal_demand import (
    LocalSpanAnalysis,
    context_groups,
    endpoint_rank_ideal,
    endpoint_transition_candidates,
    file_sha256,
    git_revision,
    has_distinct_representatives,
    write_atomic,
)
from enumerate_reflected_transition_hall import oriented_candidates, reflected_ideal


BITS = int("3218f2140c78bf", 16)
SUPPORT = int("ff", 16)
LOWER = int("aa", 16)
MAXIMUM_N = 8
STRONG_SIZE = 6
COLOR = 0
RANK = 3
FRONTIER = ((0, 3), (1, 4), (2, 5), (3, 6), (4, 7))


def active_representative(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    left: int,
    right: int,
) -> int:
    left_lower = bool(LOWER & (1 << left))
    future_left = endpoint_rank_ideal(
        local, vertices, left, COLOR, RANK, STRONG_SIZE, False
    )
    past_right = endpoint_rank_ideal(
        local, vertices, right, COLOR, RANK, STRONG_SIZE, True
    )
    answer = future_left if (COLOR == 1) == left_lower else past_right
    if not left_lower:
        answer = reflected_ideal(answer, RANK - 1, STRONG_SIZE - RANK - 1)
    return answer


def counterexample_record() -> dict[str, object]:
    analyzer = LocalSpanAnalysis(MAXIMUM_N, STRONG_SIZE)
    local = analyzer.analyze(BITS, SUPPORT)
    if local is None:
        raise AssertionError("frozen support unexpectedly contains a strong six")
    group = next(
        candidate
        for candidate in context_groups(local, SUPPORT, LOWER, MAXIMUM_N)
        if candidate == (COLOR, RANK, FRONTIER)
    )
    _, _, frontier = group
    vertices = tuple(i for i in range(MAXIMUM_N) if SUPPORT & (1 << i))
    original, left_intervals, right_intervals, _ = endpoint_transition_candidates(
        local, vertices, frontier, COLOR, RANK, STRONG_SIZE
    )
    reflected = oriented_candidates(
        original, frontier, LOWER, RANK - 1, STRONG_SIZE - RANK - 1
    )
    active = tuple(
        left_family if (COLOR == 1) == bool(LOWER & (1 << left)) else right_family
        for (left, _), left_family, right_family in zip(
            frontier, left_intervals, right_intervals, strict=True
        )
    )
    reflected_active = oriented_candidates(
        active, frontier, LOWER, RANK - 1, STRONG_SIZE - RANK - 1
    )
    representatives = tuple(
        active_representative(local, vertices, left, right)
        for left, right in frontier
    )
    for representative, family in zip(representatives, reflected, strict=True):
        if representative not in family:
            raise AssertionError("active representative left its candidate family")
    classes: dict[int, list[list[int]]] = {}
    for span, representative in zip(frontier, representatives, strict=True):
        classes.setdefault(representative, []).append(list(span))
    collision_classes = [
        spans for _, spans in sorted(classes.items()) if len(spans) > 1
    ]
    candidate_union = sorted({ideal for family in reflected for ideal in family})
    active_candidate_union = sorted(
        {ideal for family in reflected_active for ideal in family}
    )
    return {
        "maximum_n": MAXIMUM_N,
        "strong_size": STRONG_SIZE,
        "support_mask_hex": f"{SUPPORT:x}",
        "lower_mask_hex": f"{LOWER:x}",
        "coloring_hex": f"{BITS:x}",
        "color": "cap",
        "rank": RANK,
        "frontier": [list(span) for span in frontier],
        "active_representatives_hex": [f"{ideal:x}" for ideal in representatives],
        "collision_classes": collision_classes,
        "active_representative_injective": len(collision_classes) == 0,
        "reflected_candidate_union_hex": [f"{ideal:x}" for ideal in candidate_union],
        "reflected_candidate_union_card": len(candidate_union),
        "reflected_active_candidates_hex": [
            [f"{ideal:x}" for ideal in family] for family in reflected_active
        ],
        "reflected_active_candidate_union_hex": [
            f"{ideal:x}" for ideal in active_candidate_union
        ],
        "reflected_active_candidate_union_card": len(active_candidate_union),
        "frontier_card": len(frontier),
        "reflected_hall": has_distinct_representatives(reflected),
        "reflected_active_hall": has_distinct_representatives(reflected_active),
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_active_reflected_representative.py"
    parent = repo / "data/derived/e3-allocated-span-pascal-demand-k6-n8.json"
    return {
        "schema_version": 1,
        "experiment": "active-reflected-representative-counterexample",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "target": (
                "injectivity of the deterministic active-ray representative "
                "on every consecutive exact-rank frontier block"
            ),
            "decision": (
                "refute the shortcut when the active representatives collide "
                "while the complete reflected candidate family still passes Hall"
            ),
            "claim_boundary": (
                "bounded computational counterexample to active representative "
                "injectivity only; not a counterexample to block expansion"
            ),
        },
        "counterexample": counterexample_record(),
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "parent_manifest": {
                "path": str(parent.relative_to(repo)),
                "sha256": file_sha256(parent),
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
