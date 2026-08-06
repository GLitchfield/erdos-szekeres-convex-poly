#!/usr/bin/env python3
"""Independently replay the singleton-or-block-large profile gate."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_allocated_span_pascal_demand import (
    Replay,
    file_sha256,
    groups,
    height_mask_hex,
    replay_transition_candidates,
)


Tree = int | tuple["Tree", "Tree"]
LOWER_TREE: Tree = ((8, (2, 1)), ((4, 7), 10))
UPPER_TREE: Tree = (((0, 3), ((6, 9), 5)), 11)
TREE: Tree = (LOWER_TREE, UPPER_TREE)
Ideal = tuple[int, ...]


def vertices(tree: Tree) -> tuple[int, ...]:
    if isinstance(tree, int):
        return (tree,)
    return tuple(sorted(vertices(tree[0]) + vertices(tree[1])))


def coloring_bits(tree: Tree, machine: Replay) -> int:
    if isinstance(tree, int):
        return 0
    left, right = tree
    support = sum(1 << vertex for vertex in vertices(tree))
    lower = sum(1 << vertex for vertex in vertices(left))
    return coloring_bits(left, machine) | coloring_bits(right, machine) | machine.crossing(
        support, lower
    )


def reflected(ideal: Ideal, columns: int) -> Ideal:
    return tuple(columns - height for height in reversed(ideal))


def profile_record(
    color: int,
    rank: int,
    frontier: tuple[tuple[int, int], ...],
    candidates: tuple[tuple[Ideal, ...], ...],
    columns: int,
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
                        "ideal_hex": height_mask_hex(ideal, columns),
                        **owner_record,
                    }
                )
        singleton_records.append(
            {
                "singleton_index": singleton,
                "singleton_span": list(frontier[singleton]),
                "ideal_hex": height_mask_hex(ideal, columns),
                "other_owners": owners,
            }
        )
    return {
        "color": "cup" if color else "cap",
        "rank": rank,
        "block_size": block_size,
        "frontier": [list(span) for span in frontier],
        "candidate_families_hex": [
            sorted(
                (height_mask_hex(ideal, columns) for ideal in family),
                key=lambda encoded: int(encoded, 16),
            )
            for family in candidates
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
    machine = Replay(maximum_n, strong_size)
    support_vertices = vertices(TREE)
    support = sum(1 << vertex for vertex in support_vertices)
    lower = sum(1 << vertex for vertex in vertices(LOWER_TREE))
    bits = coloring_bits(TREE, machine)
    local = machine.ranks(bits, support)
    if local is None:
        raise AssertionError("frozen root unexpectedly contains a strong seven")
    records = []
    for color, rank, frontier in groups(local, support, lower, maximum_n):
        original, _, _, _ = replay_transition_candidates(
            local, support_vertices, frontier, color, rank, strong_size
        )
        columns = strong_size - rank - 1
        candidates = []
        for span, family in zip(frontier, original, strict=True):
            if lower & (1 << span[0]):
                oriented = family
            else:
                oriented = tuple(sorted(reflected(ideal, columns)
                                        for ideal in family))
            candidates.append(oriented)
        records.append(profile_record(
            color, rank, frontier, tuple(candidates), columns
        ))
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
    if replay != manifest["frozen_n12_k7"]:
        raise AssertionError("independent singleton-large profile replay differs")
    print(
        "groups=", replay["group_count"],
        "all_groups_pass=", replay["all_groups_pass"],
        "profiles=", [group["family_sizes"] for group in replay["groups"]],
    )


if __name__ == "__main__":
    main()
