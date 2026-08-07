#!/usr/bin/env python3
"""Independently replay the all-root k=8 block-large and anchor-shape gate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_allocated_span_pascal_demand import file_sha256
from check_block_large_reached_owner_all_roots import census, first_differences


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    repo = Path(__file__).resolve().parent.parent
    for source in manifest["sources"].values():
        path = repo / source["path"]
        if file_sha256(path) != source["sha256"]:
            raise SystemExit(f"source hash disagrees for {source['path']}")
    if args.source_only:
        print(f"verified sources for {args.manifest} ({file_sha256(args.manifest)})")
        return
    expected = manifest["k8_census"]
    actual = census(
        int(expected["maximum_n"]),
        int(expected["minimum_support_size"]),
        int(expected["maximum_support_size"]),
        bool(expected["stop_on_failure"]),
        8,
    )
    if actual != expected:
        details = "\n".join(first_differences(expected, actual, "k8_census"))
        raise SystemExit(f"independent k=8 replay disagrees with manifest\n{details}")
    print(f"verified {args.manifest} ({file_sha256(args.manifest)})")


if __name__ == "__main__":
    main()
