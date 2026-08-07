#!/usr/bin/env python3
"""Run the block-large and deficient-anchor gate for k=8 through eight vertices."""

from __future__ import annotations

import argparse
from pathlib import Path

from enumerate_allocated_span_pascal_demand import file_sha256, git_revision, write_atomic
from enumerate_block_large_reached_owner_all_roots import census


def produce(repo: Path, maximum_n: int) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_block_large_reached_owner_all_roots_k8.py"
    mask_base = repo / "scripts/enumerate_block_large_reached_owner_all_roots.py"
    height_base = repo / "scripts/check_block_large_reached_owner_all_roots.py"
    return {
        "schema_version": 1,
        "experiment": "all-root-block-large-reached-owner-k8-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "domain": (
                "every recursively decomposable k=8 root through the recorded "
                "support size, every reflected exact-rank consecutive frontier "
                "block, and every hole"
            ),
            "success": (
                "the block-large reached-owner profile holds, and the selected "
                "minimum deficient anchor is a one-lane saturated interval of "
                "size at most two"
            ),
            "claim_boundary": (
                "bounded k=8 computational evidence only; no arbitrary genuine-"
                "frontier profile, path-certificate theorem, Hall theorem, or "
                "exact-formula conclusion"
            ),
        },
        "k8_census": census(maximum_n, 2, maximum_n, True, 8),
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "mask_base": {
                "path": str(mask_base.relative_to(repo)),
                "sha256": file_sha256(mask_base),
            },
            "height_base": {
                "path": str(height_base.relative_to(repo)),
                "sha256": file_sha256(height_base),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-n", type=int, default=8)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 2 <= args.maximum_n <= 8:
        raise SystemExit("maximum-n must lie between 2 and 8")
    repo = Path(__file__).resolve().parent.parent
    write_atomic(args.output, produce(repo, args.maximum_n))
    print(args.output)


if __name__ == "__main__":
    main()
