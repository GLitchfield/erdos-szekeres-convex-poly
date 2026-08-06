#!/usr/bin/env python3
"""Produce the frozen two-step ownership-augmentation gate.

For a blocked one-hole state, inspect the current owner of each hole
candidate.  A candidate gives a two-step exit when its owner has an ideal
unused by the current partial representative system.  The deterministic rule
chooses the first such candidate and then the first such fresh ideal in
row-boundary order.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path

from check_singleton_large_owner_profile import frozen_record as mask_profiles
from check_stable_ownership_hole_descent import (
    enumerate_hole_states,
    ideal_boundary,
)
from enumerate_allocated_span_pascal_demand import (
    file_sha256,
    git_revision,
    write_atomic,
)


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


def two_step_exits(
    state: State,
    candidates: tuple[tuple[int, ...], ...],
    rows: int,
    columns: int,
) -> tuple[tuple[int, int, tuple[int, ...]], ...]:
    hole = state.index(-1)
    occupied = {ideal for ideal in state if ideal != -1}
    owner = {ideal: index for index, ideal in enumerate(state) if ideal != -1}
    exits = []
    for ideal in sorted(candidates[hole],
                        key=lambda value: priority(value, rows, columns)):
        if ideal not in owner:
            raise AssertionError("two-step exits are requested only for blocked states")
        displaced = owner[ideal]
        fresh = tuple(sorted(
            (value for value in candidates[displaced] if value not in occupied),
            key=lambda value: priority(value, rows, columns),
        ))
        if fresh:
            exits.append((ideal, displaced, fresh))
    return tuple(exits)


def analyze_group(group: dict[str, object], strong_size: int) -> dict[str, object]:
    rank = group["rank"]
    rows = rank - 1
    columns = strong_size - rank - 1
    candidates = tuple(
        tuple(int(encoded, 16) for encoded in family)
        for family in group["candidate_families_hex"]
    )
    states = enumerate_hole_states(candidates)
    directly_fillable = 0
    blocked = 0
    exit_histogram: Counter[int] = Counter()
    first_exit = None
    first_failure = None
    for state in states:
        hole = state.index(-1)
        occupied = {ideal for ideal in state if ideal != -1}
        if any(ideal not in occupied for ideal in candidates[hole]):
            directly_fillable += 1
            continue
        blocked += 1
        exits = two_step_exits(state, candidates, rows, columns)
        exit_histogram[len(exits)] += 1
        if not exits:
            if first_failure is None:
                first_failure = state_record(state)
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
                "state": state_record(state),
                "transferred_ideal_hex": f"{ideal:x}",
                "displaced_owner_index": owner,
                "fresh_ideal_hex": f"{fresh:x}",
                "completed_representatives_hex": [f"{value:x}" for value in completed],
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
    profiles = mask_profiles()
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


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_two_step_ownership_augmentation.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-two-step-ownership-augmentation-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "direct_exit": "the hole has an ideal unused by the current representatives",
            "two_step_exit": (
                "the hole takes an occupied candidate whose unique owner has "
                "an ideal unused by the original partial representative system"
            ),
            "deterministic_choice": (
                "first exit candidate and then first fresh ideal in ascending "
                "row-boundary order, with cell-mask tie-break"
            ),
            "claim_boundary": (
                "bounded all-state frozen-root gate; no arbitrary-frontier "
                "two-step augmentation or reflected Hall conclusion"
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
            "mask_profile": {
                "path": "scripts/check_singleton_large_owner_profile.py",
                "sha256": file_sha256(
                    repo / "scripts/check_singleton_large_owner_profile.py"
                ),
            },
            "height_profile": {
                "path": "scripts/replay_singleton_large_owner_profile.py",
                "sha256": file_sha256(
                    repo / "scripts/replay_singleton_large_owner_profile.py"
                ),
            },
            "mask_state_enumerator": {
                "path": "scripts/check_stable_ownership_hole_descent.py",
                "sha256": file_sha256(
                    repo / "scripts/check_stable_ownership_hole_descent.py"
                ),
            },
            "height_state_enumerator": {
                "path": "scripts/replay_stable_ownership_hole_descent.py",
                "sha256": file_sha256(
                    repo / "scripts/replay_stable_ownership_hole_descent.py"
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
