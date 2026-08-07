#!/usr/bin/env python3
"""Refute the deterministic reflected facing-lane gap-witness rule."""

from __future__ import annotations

import argparse
from pathlib import Path

from check_block_large_reached_owner import boundary_slot, frozen_groups
from enumerate_allocated_span_pascal_demand import file_sha256, git_revision, write_atomic
from enumerate_reflected_transition_hall import reflected_ideal


def normalized_lane(
    geometry: dict[str, object], side: str, rows: int, columns: int
) -> tuple[int, ...]:
    lane = geometry[f"{side}_lane"]
    ideals = tuple(int(encoded, 16) for encoded in lane["raw_interval_hex"])
    if geometry["reflected"]:
        ideals = tuple(
            reflected_ideal(ideal, rows, columns) for ideal in ideals
        )
    return tuple(
        sorted(
            set(ideals),
            key=lambda ideal: (boundary_slot(ideal, rows, columns), ideal),
        )
    )


def frozen_record() -> dict[str, object]:
    group = next(
        record
        for record in frozen_groups()
        if record["color"] == "cap" and record["rank"] == 3
    )
    rows = 2
    columns = 3
    block = tuple(group["frontier"])
    candidates = tuple(group["candidates"])
    geometry = tuple(group["geometry"])
    hole = 2
    hole_family = candidates[hole]
    if hole_family != (0x3F,):
        raise AssertionError("unexpected frozen minimum hole")
    owner_map = {0x3F: 1}
    if 0x3F not in candidates[1]:
        raise AssertionError("frozen owner map is not membership-feasible")
    owner_indices = set(owner_map.values())
    unmapped = tuple(index for index in range(len(block)) if index not in owner_indices)
    selected: set[int] = set()
    steps = []
    failure = None
    for gap in unmapped:
        owner = min(owner_indices, key=lambda index: (abs(index - gap), index))
        side = "left" if gap < owner else "right"
        lane = normalized_lane(geometry[owner], side, rows, columns)
        eligible = tuple(
            ideal
            for ideal in lane
            if ideal not in hole_family and ideal not in selected
        )
        step = {
            "gap_index": gap,
            "gap_span": list(block[gap]),
            "charged_owner_index": owner,
            "charged_owner_span": list(block[owner]),
            "facing_lane": side,
            "owner_reflected": geometry[owner]["reflected"],
            "normalized_lane_hex": [f"{ideal:x}" for ideal in lane],
            "eligible_hex": [f"{ideal:x}" for ideal in eligible],
        }
        if not eligible:
            step["selected_hex"] = None
            failure = {
                "reason": "no_fresh_facing_lane_candidate",
                "gap_index": gap,
                "charged_owner_index": owner,
            }
            steps.append(step)
            break
        chosen = eligible[0]
        selected.add(chosen)
        step["selected_hex"] = f"{chosen:x}"
        steps.append(step)
    if failure is None:
        raise AssertionError("facing-lane rule unexpectedly passed")
    return {
        "color": "cap",
        "rank": 3,
        "block": [list(span) for span in block],
        "hole_index": hole,
        "hole_family_hex": [f"{ideal:x}" for ideal in hole_family],
        "owner_map": [
            {"ideal_hex": f"{ideal:x}", "owner_index": owner}
            for ideal, owner in owner_map.items()
        ],
        "unmapped_positions": list(unmapped),
        "algorithm": {
            "gap_order": "increasing block index",
            "owner_choice": "nearest mapped owner, then smaller owner index",
            "lane_choice": "left when gap is left of owner, otherwise right",
            "ideal_choice": (
                "lexicographically first normalized boundary slot outside the "
                "hole family and prior charges"
            ),
        },
        "steps": steps,
        "passes": False,
        "first_failure": failure,
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_reflected_facing_lane_gap_witness.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-reflected-facing-lane-gap-witness",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "rule": (
                "charge each unmapped position to its nearest mapped owner, use "
                "the endpoint lane facing the gap, and greedily choose the first "
                "fresh normalized boundary-slot ideal"
            ),
            "success": "the rule supplies one distinct owner-star ideal per gap",
            "claim_boundary": (
                "negative control for this deterministic facing-lane rule only; "
                "no refutation of arbitrary gap witnesses or owner-star expansion"
            ),
        },
        "frozen_cap_minimum": frozen_record(),
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "mask_geometry": {
                "path": "scripts/check_block_large_reached_owner.py",
                "sha256": file_sha256(
                    repo / "scripts/check_block_large_reached_owner.py"
                ),
            },
            "height_geometry": {
                "path": "scripts/replay_block_large_reached_owner.py",
                "sha256": file_sha256(
                    repo / "scripts/replay_block_large_reached_owner.py"
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
