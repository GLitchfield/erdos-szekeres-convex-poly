#!/usr/bin/env python3
"""Independently replay the two-step ownership-augmentation gate."""

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
        sum(bool(mask & (1 << (row * columns + column)))
            for column in range(columns))
        for row in range(rows)
    )
    if any(heights[index] < heights[index + 1]
           for index in range(len(heights) - 1)):
        raise AssertionError("serialized mask is not a lower ideal")
    return heights


def state_record(state: State, columns: int) -> dict[str, object]:
    return {
        "hole_index": state.index(None),
        "representatives_hex": [
            None if ideal is None else height_mask_hex(ideal, columns)
            for ideal in state
        ],
    }


def two_step_exits(
    state: State,
    candidates: tuple[tuple[Ideal, ...], ...],
) -> tuple[tuple[Ideal, int, tuple[Ideal, ...]], ...]:
    hole = state.index(None)
    occupied = {ideal for ideal in state if ideal is not None}
    owner = {ideal: index for index, ideal in enumerate(state)
             if ideal is not None}
    exits = []
    for ideal in sorted(candidates[hole]):
        if ideal not in owner:
            raise AssertionError("two-step exits are requested only for blocked states")
        displaced = owner[ideal]
        fresh = tuple(sorted(
            value for value in candidates[displaced] if value not in occupied
        ))
        if fresh:
            exits.append((ideal, displaced, fresh))
    return tuple(exits)


def analyze_group(group: dict[str, object], strong_size: int) -> dict[str, object]:
    rank = group["rank"]
    rows = rank - 1
    columns = strong_size - rank - 1
    candidates = tuple(
        tuple(mask_heights(encoded, rows, columns) for encoded in family)
        for family in group["candidate_families_hex"]
    )
    states = enumerate_hole_states(candidates)
    directly_fillable = 0
    blocked = 0
    exit_histogram: Counter[int] = Counter()
    first_exit = None
    first_failure = None
    for state in states:
        hole = state.index(None)
        occupied = {ideal for ideal in state if ideal is not None}
        if any(ideal not in occupied for ideal in candidates[hole]):
            directly_fillable += 1
            continue
        blocked += 1
        exits = two_step_exits(state, candidates)
        exit_histogram[len(exits)] += 1
        if not exits:
            if first_failure is None:
                first_failure = state_record(state, columns)
            continue
        ideal, owner, fresh_options = exits[0]
        fresh = fresh_options[0]
        completed = list(state)
        completed[hole] = ideal
        completed[owner] = fresh
        if len(set(completed)) != len(completed):
            raise AssertionError("two-step completion is not injective")
        if any(completed[index] not in candidates[index]
               for index in range(len(candidates))):
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
        "color": group["color"],
        "rank": rank,
        "block_size": group["block_size"],
        "frontier": group["frontier"],
        "candidate_families_hex": group["candidate_families_hex"],
        "family_sizes": group["family_sizes"],
        "state_count": len(states),
        "directly_fillable_state_count": directly_fillable,
        "blocked_state_count": blocked,
        "two_step_exit_candidate_count_histogram": {
            str(count): frequency
            for count, frequency in sorted(exit_histogram.items())
        },
        "minimum_two_step_exit_candidates": (
            min(exit_histogram) if exit_histogram else None
        ),
        "all_blocked_have_two_step_exit": first_failure is None,
        "first_two_step_exit": first_exit,
        "first_failure": first_failure,
    }


def frozen_record() -> dict[str, object]:
    profiles = height_profiles()
    groups = [analyze_group(group, profiles["strong_size"])
              for group in profiles["groups"]]
    return {
        "maximum_n": profiles["maximum_n"],
        "strong_size": profiles["strong_size"],
        "support_mask_hex": profiles["support_mask_hex"],
        "lower_mask_hex": profiles["lower_mask_hex"],
        "coloring_hex": profiles["coloring_hex"],
        "group_count": len(groups),
        "state_count": sum(group["state_count"] for group in groups),
        "directly_fillable_state_count": sum(
            group["directly_fillable_state_count"] for group in groups
        ),
        "blocked_state_count": sum(group["blocked_state_count"] for group in groups),
        "all_blocked_have_two_step_exit": all(
            group["all_blocked_have_two_step_exit"] for group in groups
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
        raise AssertionError("independent two-step ownership replay differs")
    print(
        "states=", replay["state_count"],
        "blocked=", replay["blocked_state_count"],
        "all_blocked_have_two_step_exit=",
        replay["all_blocked_have_two_step_exit"],
    )


if __name__ == "__main__":
    main()
