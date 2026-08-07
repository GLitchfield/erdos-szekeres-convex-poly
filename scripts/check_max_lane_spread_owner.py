#!/usr/bin/env python3
"""Extract a counterexample to paying block demand with one lane spread."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from enumerate_allocated_span_pascal_demand import file_sha256, git_revision, write_atomic


def lane_spread(lane: dict[str, object]) -> int:
    past = int(lane["past"]["ideal_hex"], 16)
    future = int(lane["future"]["ideal_hex"], 16)
    return (past ^ future).bit_count()


def geometry_spread(geometry: dict[str, object]) -> dict[str, object]:
    left = lane_spread(geometry["left_lane"])
    right = lane_spread(geometry["right_lane"])
    return {
        "left_lane_spread": left,
        "right_lane_spread": right,
        "maximum_lane_spread": max(left, right),
        "geometry": geometry,
    }


def first_counterexample(source: dict[str, object]) -> dict[str, object] | None:
    for group_index, group in enumerate(source["frozen_n12_k7"]["groups"]):
        full_geometry = group["full_span_geometry"]
        for block_index, block in enumerate(group["blocks"]):
            block_size = int(block["block_size"])
            start = int(block["start_index"])
            for hole in block["holes"]:
                witness = hole["first_minimum_witness"]
                if witness is None or not witness["owner_map"]:
                    continue
                owners = []
                all_small_spread = True
                for mapping in witness["owner_map"]:
                    owner = int(mapping["owner_index"])
                    spread = geometry_spread(full_geometry[start + owner])
                    all_small_spread &= spread["maximum_lane_spread"] + 1 < block_size
                    owners.append({**mapping, **spread})
                if all_small_spread:
                    return {
                        "group_index": group_index,
                        "block_index": block_index,
                        "color": group["color"],
                        "rank": group["rank"],
                        "block_start_index": start,
                        "block_stop_index": block["stop_index"],
                        "block_size": block_size,
                        "block_frontier": block["frontier"],
                        "hole_index": hole["hole_index"],
                        "hole_span": hole["hole_span"],
                        "hole_family_hex": hole["candidate_family_hex"],
                        "owner_map": owners,
                        "maximum_reached_lane_spread_add_one": max(
                            owner["maximum_lane_spread"] + 1 for owner in owners
                        ),
                        "all_reached_lane_spreads_too_small": True,
                    }
    return None


def produce(repo: Path, source_path: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_max_lane_spread_owner.py"
    source = json.loads(source_path.read_text())
    counterexample = first_counterexample(source)
    if counterexample is None:
        raise AssertionError("the frozen manifest has no lane-spread counterexample")
    return {
        "schema_version": 1,
        "experiment": "frozen-max-lane-spread-owner-counterexample",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "proposed_claim": (
                "every feasible owner map reaches an owner whose maximum raw "
                "endpoint-lane cell spread plus one is at least the block size"
            ),
            "spread": (
                "the number of cells in the symmetric difference of one "
                "endpoint lane's past and future Pascal-grid ideals"
            ),
            "claim_boundary": (
                "one frozen genuine counterexample refutes only the single-lane "
                "spread bridge, not block-large reached ownership"
            ),
        },
        "counterexample": counterexample,
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "block_large_manifest": {
                "path": str(source_path.relative_to(repo)),
                "sha256": file_sha256(source_path),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--source",
        type=Path,
        default=Path("data/derived/e3-block-large-reached-owner-frozen-n12-k7.json"),
    )
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    write_atomic(args.output, produce(repo, repo / args.source))
    print(args.output)


if __name__ == "__main__":
    main()
