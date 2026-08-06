#!/usr/bin/env python3
"""Independently replay the active-representative counterexample."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_allocated_span_pascal_demand import (
    Replay,
    endpoint_rank_heights,
    file_sha256,
    groups,
    height_mask_hex,
    replay_distinct_representatives,
    replay_transition_candidates,
)
from check_reflected_transition_hall import oriented_candidates, reflected_heights


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
) -> tuple[int, ...]:
    columns = STRONG_SIZE - RANK - 1
    left_lower = bool(LOWER & (1 << left))
    future_left = endpoint_rank_heights(
        local, vertices, left, COLOR, RANK, STRONG_SIZE, False
    )
    past_right = endpoint_rank_heights(
        local, vertices, right, COLOR, RANK, STRONG_SIZE, True
    )
    answer = future_left if (COLOR == 1) == left_lower else past_right
    return answer if left_lower else reflected_heights(answer, columns)


def counterexample_record() -> dict[str, object]:
    machine = Replay(MAXIMUM_N, STRONG_SIZE)
    local = machine.ranks(BITS, SUPPORT)
    if local is None:
        raise AssertionError("frozen support unexpectedly contains a strong six")
    group = next(
        candidate
        for candidate in groups(local, SUPPORT, LOWER, MAXIMUM_N)
        if candidate == (COLOR, RANK, FRONTIER)
    )
    _, _, frontier = group
    vertices = tuple(i for i in range(MAXIMUM_N) if SUPPORT & (1 << i))
    original, left_intervals, right_intervals, _ = replay_transition_candidates(
        local, vertices, frontier, COLOR, RANK, STRONG_SIZE
    )
    columns = STRONG_SIZE - RANK - 1
    reflected = oriented_candidates(original, frontier, LOWER, columns)
    active = tuple(
        left_family if (COLOR == 1) == bool(LOWER & (1 << left)) else right_family
        for (left, _), left_family, right_family in zip(
            frontier, left_intervals, right_intervals, strict=True
        )
    )
    reflected_active = oriented_candidates(active, frontier, LOWER, columns)
    representatives = tuple(
        active_representative(local, vertices, left, right)
        for left, right in frontier
    )
    for representative, family in zip(representatives, reflected, strict=True):
        if representative not in family:
            raise AssertionError("active representative left its candidate family")
    classes: dict[tuple[int, ...], list[list[int]]] = {}
    for span, representative in zip(frontier, representatives, strict=True):
        classes.setdefault(representative, []).append(list(span))
    collision_classes = [
        spans
        for representative, spans in sorted(
            classes.items(), key=lambda item: int(height_mask_hex(item[0], columns), 16)
        )
        if len(spans) > 1
    ]
    candidate_union = sorted(
        {ideal for family in reflected for ideal in family},
        key=lambda ideal: int(height_mask_hex(ideal, columns), 16),
    )
    active_candidate_union = sorted(
        {ideal for family in reflected_active for ideal in family},
        key=lambda ideal: int(height_mask_hex(ideal, columns), 16),
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
        "active_representatives_hex": [
            height_mask_hex(ideal, columns) for ideal in representatives
        ],
        "collision_classes": collision_classes,
        "active_representative_injective": len(collision_classes) == 0,
        "reflected_candidate_union_hex": [
            height_mask_hex(ideal, columns) for ideal in candidate_union
        ],
        "reflected_candidate_union_card": len(candidate_union),
        "reflected_active_candidates_hex": [
            [height_mask_hex(ideal, columns) for ideal in family]
            for family in reflected_active
        ],
        "reflected_active_candidate_union_hex": [
            height_mask_hex(ideal, columns) for ideal in active_candidate_union
        ],
        "reflected_active_candidate_union_card": len(active_candidate_union),
        "frontier_card": len(frontier),
        "reflected_hall": replay_distinct_representatives(reflected),
        "reflected_active_hall": replay_distinct_representatives(reflected_active),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported manifest schema")
    repo = Path(__file__).resolve().parent.parent
    for source in manifest["sources"].values():
        path = repo / source["path"]
        if file_sha256(path) != source["sha256"]:
            raise AssertionError(f"source hash mismatch: {source['path']}")
    replay = counterexample_record()
    if replay != manifest["counterexample"]:
        raise AssertionError("independent counterexample replay differs")
    if replay["active_representative_injective"]:
        raise AssertionError("active representative unexpectedly became injective")
    if not replay["reflected_hall"]:
        raise AssertionError("the counterexample now refutes reflected Hall")
    if not replay["reflected_active_hall"]:
        raise AssertionError("the counterexample refutes active-interval Hall")
    print(
        "replayed active representatives=",
        replay["active_representatives_hex"],
        "active_candidate_union_card=",
        replay["reflected_active_candidate_union_card"],
    )


if __name__ == "__main__":
    main()
