#!/usr/bin/env python3
"""Produce the targeted cup/rank-three stable-ownership cycle gate."""

from __future__ import annotations

import argparse
from pathlib import Path

from check_singleton_large_owner_profile import frozen_record as mask_profiles
from check_stable_ownership_hole_descent import (
    analyze_functional_graph,
    enumerate_hole_states,
)
from enumerate_allocated_span_pascal_demand import (
    file_sha256,
    git_revision,
    write_atomic,
)


def targeted_record() -> dict[str, object]:
    frozen = mask_profiles()
    group = next(
        record for record in frozen["groups"]
        if record["color"] == "cup" and record["rank"] == 3
    )
    candidates = tuple(
        tuple(int(encoded, 16) for encoded in family)
        for family in group["candidate_families_hex"]
    )
    states = enumerate_hole_states(candidates)
    return {
        "color": group["color"],
        "rank": group["rank"],
        "rows": group["rank"] - 1,
        "columns": frozen["strong_size"] - group["rank"] - 1,
        "block_size": group["block_size"],
        "frontier": group["frontier"],
        "candidate_families_hex": group["candidate_families_hex"],
        "family_sizes": group["family_sizes"],
        "functional_graph": analyze_functional_graph(
            states,
            candidates,
            group["rank"] - 1,
            frozen["strong_size"] - group["rank"] - 1,
        ),
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_stable_ownership_cup_rank3_cycle.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-stable-ownership-cup-rank-three-cycle-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "priority": (
                "ascending lexicographic row-boundary tuple with cell-mask "
                "tie-break, unchanged from experiment 0036"
            ),
            "move": (
                "an unfillable hole takes its first candidate and transfers "
                "the hole to that ideal's unique current owner"
            ),
            "failure": (
                "a directed cycle whose states are all unfillable, or an "
                "invalid successor"
            ),
            "claim_boundary": (
                "targeted frozen cup/rank-three falsifier only; no conclusion "
                "about other priorities or ownership-plus-uncrossing rules"
            ),
        },
        "frozen_n12_k7_cup_rank3": targeted_record(),
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
            "mask_graph": {
                "path": "scripts/check_stable_ownership_hole_descent.py",
                "sha256": file_sha256(
                    repo / "scripts/check_stable_ownership_hole_descent.py"
                ),
            },
            "height_graph": {
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
