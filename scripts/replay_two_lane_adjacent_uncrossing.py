#!/usr/bin/env python3
"""Independently replay the frozen adjacent meet/join uncrossing gate."""

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


def reflected(ideal: tuple[int, ...], columns: int) -> tuple[int, ...]:
    return tuple(columns - height for height in reversed(ideal))


def mask(ideal: tuple[int, ...], columns: int) -> int:
    return int(height_mask_hex(ideal, columns), 16)


def pair_example(
    group_index: int,
    adjacent_index: int,
    frontier: tuple[tuple[int, int], ...],
    first: tuple[int, ...],
    second: tuple[int, ...],
    columns: int,
) -> dict[str, object]:
    meet = tuple(min(a, b) for a, b in zip(first, second, strict=True))
    join = tuple(max(a, b) for a, b in zip(first, second, strict=True))
    return {
        "group_index": group_index,
        "adjacent_index": adjacent_index,
        "earlier_span": list(frontier[adjacent_index]),
        "later_span": list(frontier[adjacent_index + 1]),
        "earlier_ideal_hex": f"{mask(first, columns):x}",
        "later_ideal_hex": f"{mask(second, columns):x}",
        "meet_hex": f"{mask(meet, columns):x}",
        "join_hex": f"{mask(join, columns):x}",
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
    first_forward_failure = None
    first_flexible_failure = None
    total_pairs = 0
    for group_index, (color, rank, frontier) in enumerate(
        groups(local, support, lower, maximum_n)
    ):
        original, _, _, _ = replay_transition_candidates(
            local, support_vertices, frontier, color, rank, strong_size
        )
        columns = strong_size - rank - 1
        candidates = []
        for span, family in zip(frontier, original, strict=True):
            if lower & (1 << span[0]):
                oriented = family
            else:
                oriented = tuple(
                    sorted(
                        (reflected(ideal, columns) for ideal in family),
                        key=lambda ideal: mask(ideal, columns),
                    )
                )
            candidates.append(oriented)
        candidate_rows = tuple(candidates)
        adjacent_records = []
        for adjacent_index in range(len(frontier) - 1):
            earlier = set(candidate_rows[adjacent_index])
            later = set(candidate_rows[adjacent_index + 1])
            forward_count = 0
            reverse_count = 0
            both_count = 0
            pair_count = len(earlier) * len(later)
            total_pairs += pair_count
            local_forward_failure = None
            local_flexible_failure = None
            for first in sorted(earlier, key=lambda ideal: mask(ideal, columns)):
                for second in sorted(later, key=lambda ideal: mask(ideal, columns)):
                    meet = tuple(
                        min(a, b) for a, b in zip(first, second, strict=True)
                    )
                    join = tuple(
                        max(a, b) for a, b in zip(first, second, strict=True)
                    )
                    forward = meet in earlier and join in later
                    reverse = join in earlier and meet in later
                    forward_count += int(forward)
                    reverse_count += int(reverse)
                    both_count += int(forward and reverse)
                    example = pair_example(
                        group_index,
                        adjacent_index,
                        frontier,
                        first,
                        second,
                        columns,
                    )
                    if not forward and local_forward_failure is None:
                        local_forward_failure = example
                    if not (forward or reverse) and local_flexible_failure is None:
                        local_flexible_failure = example
            if first_forward_failure is None and local_forward_failure is not None:
                first_forward_failure = local_forward_failure
            if first_flexible_failure is None and local_flexible_failure is not None:
                first_flexible_failure = local_flexible_failure
            adjacent_records.append(
                {
                    "adjacent_index": adjacent_index,
                    "earlier_span": list(frontier[adjacent_index]),
                    "later_span": list(frontier[adjacent_index + 1]),
                    "candidate_pair_count": pair_count,
                    "forward_valid_count": forward_count,
                    "reverse_valid_count": reverse_count,
                    "both_valid_count": both_count,
                    "fixed_forward_all": local_forward_failure is None,
                    "flexible_either_all": local_flexible_failure is None,
                    "first_forward_failure": local_forward_failure,
                    "first_flexible_failure": local_flexible_failure,
                }
            )
        records.append(
            {
                "color": "cup" if color else "cap",
                "rank": rank,
                "frontier": [list(span) for span in frontier],
                "candidate_families_hex": [
                    [f"{mask(ideal, columns):x}" for ideal in family]
                    for family in candidate_rows
                ],
                "adjacent_pairs": adjacent_records,
            }
        )
    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "rank_group_checks": len(records),
        "candidate_pair_checks": total_pairs,
        "groups": records,
        "fixed_forward_all": first_forward_failure is None,
        "first_forward_failure": first_forward_failure,
        "flexible_either_all": first_flexible_failure is None,
        "first_flexible_failure": first_flexible_failure,
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
        raise AssertionError("independent two-lane uncrossing replay differs")
    print(
        "candidate_pair_checks=",
        replay["candidate_pair_checks"],
        "fixed_forward_all=",
        replay["fixed_forward_all"],
        "flexible_either_all=",
        replay["flexible_either_all"],
    )


if __name__ == "__main__":
    main()
