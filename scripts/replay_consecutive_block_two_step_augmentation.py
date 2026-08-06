#!/usr/bin/env python3
"""Independently replay every consecutive-block two-step augmentation gate."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

from check_allocated_span_pascal_demand import file_sha256, height_mask_hex
from replay_singleton_large_owner_profile import frozen_record as height_profiles
from replay_stable_ownership_hole_descent import enumerate_hole_states


Ideal = tuple[int, ...]
State = tuple[Ideal | None, ...]


def mask_heights(encoded: str, rows: int, columns: int) -> Ideal:
    mask = int(encoded, 16)
    heights = tuple(
        sum(bool(mask & (1 << (row * columns + column))) for column in range(columns))
        for row in range(rows)
    )
    if any(heights[index] < heights[index + 1] for index in range(len(heights) - 1)):
        raise AssertionError("serialized mask is not a lower ideal")
    return heights


def state_record(state: State, columns: int) -> dict[str, object]:
    return {
        "hole_index": state.index(None),
        "representatives_hex": [
            None if ideal is None else height_mask_hex(ideal, columns) for ideal in state
        ],
    }


def exits(
    state: State,
    candidates: tuple[tuple[Ideal, ...], ...],
) -> tuple[tuple[Ideal, int, tuple[Ideal, ...]], ...]:
    hole = state.index(None)
    occupied = {ideal for ideal in state if ideal is not None}
    owners = {ideal: index for index, ideal in enumerate(state) if ideal is not None}
    result = []
    for ideal in sorted(candidates[hole]):
        owner = owners.get(ideal)
        if owner is None:
            raise AssertionError("blocked state contains an unowned hole candidate")
        fresh = tuple(sorted(value for value in candidates[owner] if value not in occupied))
        if fresh:
            result.append((ideal, owner, fresh))
    return tuple(result)


def analyze_block(
    group: dict[str, object],
    start: int,
    stop: int,
    strong_size: int,
) -> dict[str, object]:
    rank = int(group["rank"])
    rows = rank - 1
    columns = strong_size - rank - 1
    encoded_families = group["candidate_families_hex"][start:stop]
    candidates = tuple(
        tuple(mask_heights(encoded, rows, columns) for encoded in family)
        for family in encoded_families
    )
    direct = 0
    blocked = 0
    exit_histogram: Counter[int] = Counter()
    first_exit = None
    first_failure = None
    states = enumerate_hole_states(candidates)
    for state in states:
        hole = state.index(None)
        occupied = {ideal for ideal in state if ideal is not None}
        if any(ideal not in occupied for ideal in candidates[hole]):
            direct += 1
            continue
        blocked += 1
        available = exits(state, candidates)
        exit_histogram[len(available)] += 1
        if not available:
            if first_failure is None:
                first_failure = state_record(state, columns)
            continue
        ideal, owner, fresh_options = available[0]
        fresh = fresh_options[0]
        completed = list(state)
        completed[hole] = ideal
        completed[owner] = fresh
        if len(set(completed)) != len(completed):
            raise AssertionError("two-step completion is not injective")
        if any(completed[index] not in candidates[index] for index in range(len(candidates))):
            raise AssertionError("two-step completion violates membership")
        if first_exit is None:
            first_exit = {
                "state": state_record(state, columns),
                "transferred_ideal_hex": height_mask_hex(ideal, columns),
                "displaced_owner_index": owner,
                "fresh_ideal_hex": height_mask_hex(fresh, columns),
                "completed_representatives_hex": [
                    height_mask_hex(value, columns) for value in completed
                ],
            }
    return {
        "start_index": start,
        "stop_index": stop,
        "block_size": stop - start,
        "frontier": group["frontier"][start:stop],
        "candidate_families_hex": encoded_families,
        "family_sizes": group["family_sizes"][start:stop],
        "state_count": len(states),
        "directly_fillable_state_count": direct,
        "blocked_state_count": blocked,
        "two_step_exit_candidate_count_histogram": {
            str(count): frequency for count, frequency in sorted(exit_histogram.items())
        },
        "minimum_two_step_exit_candidates": min(exit_histogram) if exit_histogram else None,
        "all_states_direct_or_two_step": first_failure is None,
        "first_two_step_exit": first_exit,
        "first_failure": first_failure,
    }


def analyze_group(group: dict[str, object], strong_size: int) -> dict[str, object]:
    size = int(group["block_size"])
    blocks = [
        analyze_block(group, start, stop, strong_size)
        for start in range(size)
        for stop in range(start + 1, size + 1)
    ]
    first_failure = next(
        (block for block in blocks if not block["all_states_direct_or_two_step"]),
        None,
    )
    return {
        "color": group["color"],
        "rank": group["rank"],
        "full_frontier": group["frontier"],
        "full_block_size": size,
        "consecutive_block_count": len(blocks),
        "state_count": sum(block["state_count"] for block in blocks),
        "directly_fillable_state_count": sum(
            block["directly_fillable_state_count"] for block in blocks
        ),
        "blocked_state_count": sum(block["blocked_state_count"] for block in blocks),
        "all_states_direct_or_two_step": first_failure is None,
        "first_failing_block": first_failure,
        "blocks": blocks,
    }


def frozen_record() -> dict[str, object]:
    profiles = height_profiles()
    groups = [analyze_group(group, profiles["strong_size"]) for group in profiles["groups"]]
    return {
        "maximum_n": profiles["maximum_n"],
        "strong_size": profiles["strong_size"],
        "support_mask_hex": profiles["support_mask_hex"],
        "lower_mask_hex": profiles["lower_mask_hex"],
        "coloring_hex": profiles["coloring_hex"],
        "group_count": len(groups),
        "consecutive_block_count": sum(group["consecutive_block_count"] for group in groups),
        "state_count": sum(group["state_count"] for group in groups),
        "directly_fillable_state_count": sum(
            group["directly_fillable_state_count"] for group in groups
        ),
        "blocked_state_count": sum(group["blocked_state_count"] for group in groups),
        "all_states_direct_or_two_step": all(
            group["all_states_direct_or_two_step"] for group in groups
        ),
        "groups": groups,
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
    replay = frozen_record()
    if replay != manifest["frozen_n12_k7"]:
        raise AssertionError("independent consecutive-block replay differs")
    print(
        "blocks=", replay["consecutive_block_count"],
        "states=", replay["state_count"],
        "blocked=", replay["blocked_state_count"],
        "all_states_direct_or_two_step=", replay["all_states_direct_or_two_step"],
    )


if __name__ == "__main__":
    main()
