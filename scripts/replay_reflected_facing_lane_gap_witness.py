#!/usr/bin/env python3
"""Independently replay the reflected facing-lane gap-witness failure."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_allocated_span_pascal_demand import file_sha256, height_mask_hex
from replay_block_large_reached_owner import frozen_groups


Ideal = tuple[int, ...]


def boundary_slot(ideal: Ideal, columns: int) -> tuple[int, ...]:
    return tuple(
        row + columns - height for row, height in enumerate(ideal)
    )


def normalized_lane(
    geometry: dict[str, object], side: str, columns: int
) -> tuple[str, ...]:
    lane = geometry[f"{side}_lane"]
    encoded = tuple(lane["raw_interval_hex"])
    if geometry["reflected"]:
        reflected = []
        rows = len(lane["past"]["boundary_slot"])
        for item in encoded:
            mask = int(item, 16)
            heights = tuple(
                sum(
                    bool(mask & (1 << (row * columns + column)))
                    for column in range(columns)
                )
                for row in range(rows)
            )
            reflected_heights = tuple(
                columns - height for height in reversed(heights)
            )
            reflected.append(height_mask_hex(reflected_heights, columns))
        encoded = tuple(reflected)

    def key(item: str) -> tuple[object, ...]:
        mask = int(item, 16)
        rows = len(lane["past"]["boundary_slot"])
        ideal = tuple(
            sum(
                bool(mask & (1 << (row * columns + column)))
                for column in range(columns)
            )
            for row in range(rows)
        )
        return boundary_slot(ideal, columns) + (mask,)

    return tuple(sorted(set(encoded), key=key))


def frozen_record() -> dict[str, object]:
    group = next(
        record
        for record in frozen_groups()
        if record["color"] == "cap" and record["rank"] == 3
    )
    columns = 3
    block = tuple(tuple(span) for span in group["frontier"])
    candidates = tuple(group["candidates"])
    geometry = tuple(group["geometry"])
    hole = 2
    hole_family = tuple(
        height_mask_hex(ideal, columns) for ideal in candidates[hole]
    )
    if hole_family != ("3f",):
        raise AssertionError("unexpected frozen minimum hole")
    owner_map = {"3f": 1}
    owner_family = tuple(
        height_mask_hex(ideal, columns) for ideal in candidates[1]
    )
    if "3f" not in owner_family:
        raise AssertionError("frozen owner map is not membership-feasible")
    owner_indices = set(owner_map.values())
    unmapped = tuple(index for index in range(len(block)) if index not in owner_indices)
    selected: set[str] = set()
    steps = []
    failure = None
    for gap in unmapped:
        owner = min(owner_indices, key=lambda index: (abs(index - gap), index))
        side = "left" if gap < owner else "right"
        lane = normalized_lane(geometry[owner], side, columns)
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
            "normalized_lane_hex": list(lane),
            "eligible_hex": list(eligible),
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
        step["selected_hex"] = chosen
        steps.append(step)
    if failure is None:
        raise AssertionError("facing-lane rule unexpectedly passed")
    return {
        "color": "cap",
        "rank": 3,
        "block": [list(span) for span in block],
        "hole_index": hole,
        "hole_family_hex": list(hole_family),
        "owner_map": [{"ideal_hex": "3f", "owner_index": 1}],
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
    if replay != manifest["frozen_cap_minimum"]:
        raise AssertionError("independent facing-lane replay differs")
    print(
        "passes=", replay["passes"],
        "failure=", replay["first_failure"]["reason"],
        "gap=", replay["first_failure"]["gap_index"],
    )


if __name__ == "__main__":
    main()
