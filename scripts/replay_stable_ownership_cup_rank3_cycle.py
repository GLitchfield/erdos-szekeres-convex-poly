#!/usr/bin/env python3
"""Independently replay the cup/rank-three stable-ownership cycle gate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_allocated_span_pascal_demand import file_sha256
from replay_singleton_large_owner_profile import frozen_record as height_profiles
from replay_stable_ownership_hole_descent import (
    analyze_functional_graph,
    enumerate_hole_states,
)


Ideal = tuple[int, ...]


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


def targeted_record() -> dict[str, object]:
    frozen = height_profiles()
    group = next(
        record for record in frozen["groups"]
        if record["color"] == "cup" and record["rank"] == 3
    )
    rows = group["rank"] - 1
    columns = frozen["strong_size"] - group["rank"] - 1
    candidates = tuple(
        tuple(mask_heights(encoded, rows, columns) for encoded in family)
        for family in group["candidate_families_hex"]
    )
    states = enumerate_hole_states(candidates)
    return {
        "color": group["color"],
        "rank": group["rank"],
        "rows": rows,
        "columns": columns,
        "block_size": group["block_size"],
        "frontier": group["frontier"],
        "candidate_families_hex": group["candidate_families_hex"],
        "family_sizes": group["family_sizes"],
        "functional_graph": analyze_functional_graph(
            states, candidates, columns
        ),
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
    replay = targeted_record()
    if replay != manifest["frozen_n12_k7_cup_rank3"]:
        raise AssertionError("independent cup/rank-three cycle replay differs")
    graph = replay["functional_graph"]
    print(
        "states=", graph["state_count"],
        "cycles=", graph["directed_cycle_count"],
        "states_reaching_cycle=", graph["states_reaching_cycle"],
        "all_reach_fillable=", graph["all_states_reach_fillable"],
    )


if __name__ == "__main__":
    main()
