#!/usr/bin/env python3
"""Check two-step ownership augmentation on every frozen consecutive block.

This is the cell-mask producer.  It reconstructs the four frozen frontier
groups, takes every nonempty consecutive subblock, enumerates every injective
one-hole state, and requires either a direct fill or a length-two augmenting
exit.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path

from check_singleton_large_owner_profile import frozen_record as mask_profiles
from check_stable_ownership_hole_descent import enumerate_hole_states, ideal_boundary
from enumerate_allocated_span_pascal_demand import file_sha256, git_revision, write_atomic


State = tuple[int, ...]


def priority(mask: int, rows: int, columns: int) -> tuple[object, ...]:
    return ideal_boundary(mask, rows, columns) + (mask,)


def state_record(state: State) -> dict[str, object]:
    return {
        "hole_index": state.index(-1),
        "representatives_hex": [
            None if ideal == -1 else f"{ideal:x}" for ideal in state
        ],
    }


def exits(
    state: State,
    candidates: tuple[tuple[int, ...], ...],
    rows: int,
    columns: int,
) -> tuple[tuple[int, int, tuple[int, ...]], ...]:
    hole = state.index(-1)
    occupied = {ideal for ideal in state if ideal != -1}
    owners = {ideal: index for index, ideal in enumerate(state) if ideal != -1}
    result = []
    for ideal in sorted(candidates[hole], key=lambda x: priority(x, rows, columns)):
        owner = owners.get(ideal)
        if owner is None:
            raise AssertionError("blocked state contains an unowned hole candidate")
        fresh = tuple(sorted(
            (value for value in candidates[owner] if value not in occupied),
            key=lambda x: priority(x, rows, columns),
        ))
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
        tuple(int(encoded, 16) for encoded in family)
        for family in encoded_families
    )
    direct = 0
    blocked = 0
    exit_histogram: Counter[int] = Counter()
    first_exit = None
    first_failure = None
    states = enumerate_hole_states(candidates)
    for state in states:
        hole = state.index(-1)
        occupied = {ideal for ideal in state if ideal != -1}
        if any(ideal not in occupied for ideal in candidates[hole]):
            direct += 1
            continue
        blocked += 1
        available = exits(state, candidates, rows, columns)
        exit_histogram[len(available)] += 1
        if not available:
            if first_failure is None:
                first_failure = state_record(state)
            continue
        ideal, owner, fresh_options = available[0]
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
                "state": state_record(state),
                "transferred_ideal_hex": f"{ideal:x}",
                "displaced_owner_index": owner,
                "fresh_ideal_hex": f"{fresh:x}",
                "completed_representatives_hex": [f"{value:x}" for value in completed],
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
    profiles = mask_profiles()
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


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_consecutive_block_two_step_augmentation.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-consecutive-block-two-step-augmentation-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "blocks": "every nonempty consecutive subblock of each frozen frontier group",
            "states": "every injective representative assignment with exactly one local hole",
            "success": "the hole is directly fillable or has a length-two ownership augmentation",
            "claim_boundary": (
                "bounded frozen-n12-k7 consecutive-block gate; no arbitrary-frontier "
                "augmentation theorem, realizability bridge, or exact-formula conclusion"
            ),
        },
        "frozen_n12_k7": frozen_record(),
        "sources": {
            "producer": {"path": str(producer.relative_to(repo)), "sha256": file_sha256(producer)},
            "checker": {"path": str(checker.relative_to(repo)), "sha256": file_sha256(checker)},
            "mask_profile": {
                "path": "scripts/check_singleton_large_owner_profile.py",
                "sha256": file_sha256(repo / "scripts/check_singleton_large_owner_profile.py"),
            },
            "height_profile": {
                "path": "scripts/replay_singleton_large_owner_profile.py",
                "sha256": file_sha256(repo / "scripts/replay_singleton_large_owner_profile.py"),
            },
            "mask_state_enumerator": {
                "path": "scripts/check_stable_ownership_hole_descent.py",
                "sha256": file_sha256(repo / "scripts/check_stable_ownership_hole_descent.py"),
            },
            "height_state_enumerator": {
                "path": "scripts/replay_stable_ownership_hole_descent.py",
                "sha256": file_sha256(repo / "scripts/replay_stable_ownership_hole_descent.py"),
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
