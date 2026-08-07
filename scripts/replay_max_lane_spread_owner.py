#!/usr/bin/env python3
"""Independently check the frozen maximum-lane-spread counterexample."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_allocated_span_pascal_demand import file_sha256


def check_sources(manifest: dict[str, object], repo: Path) -> None:
    for name, source in manifest["sources"].items():
        path = repo / source["path"]
        actual = file_sha256(path)
        if actual != source["sha256"]:
            raise SystemExit(
                f"stale {name} source: expected {source['sha256']}, got {actual}"
            )


def boundary_spread(lane: dict[str, object]) -> int:
    past = lane["past"]["boundary_slot"]
    future = lane["future"]["boundary_slot"]
    if len(past) != len(future):
        raise AssertionError("lane boundary lengths differ")
    return sum(abs(int(first) - int(second)) for first, second in zip(past, future))


def replay(manifest: dict[str, object]) -> None:
    record = manifest["counterexample"]
    block_size = int(record["block_size"])
    owners = record["owner_map"]
    if not owners:
        raise AssertionError("counterexample owner map is empty")
    maximum = 0
    seen = set()
    for owner in owners:
        owner_index = int(owner["owner_index"])
        if owner_index in seen:
            raise AssertionError("owner map is not injective")
        seen.add(owner_index)
        geometry = owner["geometry"]
        left = boundary_spread(geometry["left_lane"])
        right = boundary_spread(geometry["right_lane"])
        if left != owner["left_lane_spread"]:
            raise AssertionError("left-lane spread disagrees")
        if right != owner["right_lane_spread"]:
            raise AssertionError("right-lane spread disagrees")
        spread = max(left, right)
        if spread != owner["maximum_lane_spread"]:
            raise AssertionError("maximum lane spread disagrees")
        if spread + 1 >= block_size:
            raise AssertionError("recorded owner is not a spread-small counterexample")
        maximum = max(maximum, spread + 1)
    if maximum != record["maximum_reached_lane_spread_add_one"]:
        raise AssertionError("maximum reached spread bound disagrees")
    if not record["all_reached_lane_spreads_too_small"]:
        raise AssertionError("counterexample conclusion is false")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    repo = Path(__file__).resolve().parent.parent
    check_sources(manifest, repo)
    replay(manifest)
    print(f"verified {args.manifest} ({file_sha256(args.manifest)})")


if __name__ == "__main__":
    main()
