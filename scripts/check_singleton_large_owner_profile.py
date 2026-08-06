#!/usr/bin/env python3
"""Produce the frozen singleton-or-block-large profile gate.

This is the profile-only falsifier selected by the stable-ownership route
review.  It does not enumerate partial matchings.  For each reflected frontier
group it checks:

H1. every candidate family is a singleton or has size at least the block;
H2. every other family containing a singleton family's ideal has size at
    least the block.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from enumerate_allocated_span_pascal_demand import (
    DecomposableColorings,
    LocalSpanAnalysis,
    context_groups,
    endpoint_transition_candidates,
    file_sha256,
    git_revision,
    write_atomic,
)
from enumerate_reflected_transition_hall import (
    FROZEN_LOWER_TREE,
    FROZEN_TREE,
    oriented_candidates,
    tree_coloring_bits,
    tree_support,
)


def profile_record(
    color: int,
    rank: int,
    frontier: tuple[tuple[int, int], ...],
    candidates: tuple[tuple[int, ...], ...],
) -> dict[str, object]:
    block_size = len(frontier)
    family_sizes = [len(family) for family in candidates]
    h1_failures = [
        {
            "span_index": index,
            "span": list(frontier[index]),
            "family_size": size,
        }
        for index, size in enumerate(family_sizes)
        if size != 1 and size < block_size
    ]
    singleton_records = []
    h2_failures = []
    for singleton, family in enumerate(candidates):
        if len(family) != 1:
            continue
        ideal = family[0]
        owners = []
        for owner, owner_family in enumerate(candidates):
            if owner == singleton or ideal not in owner_family:
                continue
            owner_record = {
                "owner_index": owner,
                "owner_span": list(frontier[owner]),
                "owner_family_size": len(owner_family),
            }
            owners.append(owner_record)
            if len(owner_family) < block_size:
                h2_failures.append(
                    {
                        "singleton_index": singleton,
                        "singleton_span": list(frontier[singleton]),
                        "ideal_hex": f"{ideal:x}",
                        **owner_record,
                    }
                )
        singleton_records.append(
            {
                "singleton_index": singleton,
                "singleton_span": list(frontier[singleton]),
                "ideal_hex": f"{ideal:x}",
                "other_owners": owners,
            }
        )
    return {
        "color": "cup" if color else "cap",
        "rank": rank,
        "block_size": block_size,
        "frontier": [list(span) for span in frontier],
        "candidate_families_hex": [
            [f"{ideal:x}" for ideal in family] for family in candidates
        ],
        "family_sizes": family_sizes,
        "singleton_families": singleton_records,
        "h1_singleton_or_block_large": not h1_failures,
        "h1_failures": h1_failures,
        "h2_singleton_owners_block_large": not h2_failures,
        "h2_failures": h2_failures,
        "profile_passes": not h1_failures and not h2_failures,
    }


def frozen_record() -> dict[str, object]:
    maximum_n = 12
    strong_size = 7
    colorings = DecomposableColorings(maximum_n)
    analyzer = LocalSpanAnalysis(maximum_n, strong_size)
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    bits = tree_coloring_bits(FROZEN_TREE, colorings)
    local = analyzer.analyze(bits, support)
    if local is None:
        raise AssertionError("frozen root unexpectedly contains a strong seven")
    vertices = tuple(vertex for vertex in range(maximum_n)
                     if support & (1 << vertex))
    records = []
    for color, rank, frontier in context_groups(
        local, support, lower, maximum_n
    ):
        original, _, _, _ = endpoint_transition_candidates(
            local, vertices, frontier, color, rank, strong_size
        )
        candidates = oriented_candidates(
            original, frontier, lower, rank - 1,
            strong_size - rank - 1
        )
        records.append(profile_record(color, rank, frontier, candidates))
    failures = [
        {"group_index": index, "color": record["color"], "rank": record["rank"]}
        for index, record in enumerate(records)
        if not record["profile_passes"]
    ]
    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "group_count": len(records),
        "groups": records,
        "all_groups_pass": not failures,
        "failures": failures,
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_singleton_large_owner_profile.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-singleton-or-block-large-owner-profile",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "h1": (
                "each reflected two-endpoint candidate family is a singleton "
                "or has cardinality at least its frontier block"
            ),
            "h2": (
                "every other family containing a singleton family's ideal "
                "has cardinality at least its frontier block"
            ),
            "claim_boundary": (
                "profile-only frozen-root gate; no partial matching census, "
                "arbitrary-frontier Hall claim, or geometric derivation"
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
            "base_producer": {
                "path": "scripts/enumerate_allocated_span_pascal_demand.py",
                "sha256": file_sha256(
                    repo / "scripts/enumerate_allocated_span_pascal_demand.py"
                ),
            },
            "base_checker": {
                "path": "scripts/check_allocated_span_pascal_demand.py",
                "sha256": file_sha256(
                    repo / "scripts/check_allocated_span_pascal_demand.py"
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
