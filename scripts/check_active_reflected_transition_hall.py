#!/usr/bin/env python3
"""Independently replay the active reflected transition-Hall gate."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

from check_allocated_span_pascal_demand import (
    Replay,
    file_sha256,
    groups,
    height_mask_hex,
    proper_parts,
    replay_distinct_representatives,
    replay_transition_candidates,
)
from check_reflected_transition_hall import oriented_candidates


Tree = int | tuple["Tree", "Tree"]

FROZEN_LOWER_TREE: Tree = ((8, (2, 1)), ((4, 7), 10))
FROZEN_UPPER_TREE: Tree = (((0, 3), ((6, 9), 5)), 11)
FROZEN_TREE: Tree = (FROZEN_LOWER_TREE, FROZEN_UPPER_TREE)


def tree_support(tree: Tree) -> int:
    if isinstance(tree, int):
        return 1 << tree
    return tree_support(tree[0]) | tree_support(tree[1])


def tree_coloring_bits(tree: Tree, machine: Replay) -> int:
    if isinstance(tree, int):
        return 0
    lower, upper = tree
    support = tree_support(tree)
    lower_support = tree_support(lower)
    return (
        tree_coloring_bits(lower, machine)
        | tree_coloring_bits(upper, machine)
        | machine.crossing(support, lower_support)
    )


def active_reflected_candidates(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    frontier: tuple[tuple[int, int], ...],
    lower: int,
    color: int,
    rank: int,
    strong_size: int,
) -> tuple[tuple[tuple[int, ...], ...], ...]:
    _, left_intervals, right_intervals, _ = replay_transition_candidates(
        local, vertices, frontier, color, rank, strong_size
    )
    active = tuple(
        left_family if (color == 1) == bool(lower & (1 << left)) else right_family
        for (left, _), left_family, right_family in zip(
            frontier, left_intervals, right_intervals, strict=True
        )
    )
    return oriented_candidates(
        active, frontier, lower, strong_size - rank - 1
    )


def first_consecutive_block_defect(
    frontier: tuple[tuple[int, int], ...],
    candidates: tuple[tuple[tuple[int, ...], ...], ...],
    columns: int,
) -> dict[str, object] | None:
    key = lambda ideal: int(height_mask_hex(ideal, columns), 16)
    for first in range(len(frontier)):
        candidate_union: set[tuple[int, ...]] = set()
        for last in range(first, len(frontier)):
            candidate_union.update(candidates[last])
            block_card = last - first + 1
            if block_card > len(candidate_union):
                return {
                    "first_index": first,
                    "last_index": last,
                    "spans": [list(span) for span in frontier[first : last + 1]],
                    "candidate_families_hex": [
                        [height_mask_hex(ideal, columns) for ideal in family]
                        for family in candidates[first : last + 1]
                    ],
                    "block_card": block_card,
                    "candidate_union_hex": [
                        height_mask_hex(ideal, columns)
                        for ideal in sorted(candidate_union, key=key)
                    ],
                    "candidate_union_card": len(candidate_union),
                }
    return None


def group_record(
    support: int,
    lower: int,
    bits: int,
    color: int,
    rank: int,
    frontier: tuple[tuple[int, int], ...],
    candidates: tuple[tuple[tuple[int, ...], ...], ...],
    strong_size: int,
) -> dict[str, object]:
    columns = strong_size - rank - 1
    key = lambda ideal: int(height_mask_hex(ideal, columns), 16)
    candidate_union = sorted(
        {ideal for family in candidates for ideal in family}, key=key
    )
    defect = first_consecutive_block_defect(frontier, candidates, columns)
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "color": "cup" if color else "cap",
        "rank": rank,
        "frontier": [list(span) for span in frontier],
        "active_reflected_candidates_hex": [
            [height_mask_hex(ideal, columns) for ideal in family]
            for family in candidates
        ],
        "frontier_card": len(frontier),
        "candidate_union_card": len(candidate_union),
        "consecutive_block_expansion": defect is None,
        "first_consecutive_block_defect": defect,
        "full_frontier_matching": replay_distinct_representatives(candidates),
    }


def analyze_root(
    machine: Replay,
    bits: int,
    support: int,
    lower: int,
) -> tuple[list[dict[str, object]] | None, dict[str, object] | None]:
    local = machine.ranks(bits, support)
    if local is None:
        return None, None
    vertices = tuple(
        vertex
        for vertex in range(machine.maximum_n)
        if support & (1 << vertex)
    )
    records = []
    first_failure = None
    for color, rank, frontier in groups(
        local, support, lower, machine.maximum_n
    ):
        candidates = active_reflected_candidates(
            local,
            vertices,
            frontier,
            lower,
            color,
            rank,
            machine.strong_size,
        )
        record = group_record(
            support,
            lower,
            bits,
            color,
            rank,
            frontier,
            candidates,
            machine.strong_size,
        )
        records.append(record)
        if not record["consecutive_block_expansion"] and first_failure is None:
            first_failure = record
    return records, first_failure


def frozen_gate() -> dict[str, object]:
    machine = Replay(12, 7)
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    bits = tree_coloring_bits(FROZEN_TREE, machine)
    records, failure = analyze_root(machine, bits, support, lower)
    if records is None:
        raise AssertionError("frozen collision unexpectedly contains a strong seven")
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "rank_group_checks": len(records),
        "consecutive_block_expansion": failure is None,
        "first_block_failure": failure,
    }


def k6_gate(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    machine = Replay(maximum_n, 6)
    full = (1 << maximum_n) - 1
    machine.colorings(full)
    totals: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    digest = hashlib.sha256()
    first_failure = None
    stopped = False

    for size in range(2, maximum_n + 1):
        row: Counter[str] = Counter()
        for support in range(1, full + 1):
            if support.bit_count() != size:
                continue
            for lower in proper_parts(support):
                upper = support ^ lower
                fixed = machine.crossing(support, lower)
                for lower_bits in machine.colorings(lower):
                    for upper_bits in machine.colorings(upper):
                        bits = lower_bits | upper_bits | fixed
                        row["root_contexts"] += 1
                        records, failure = analyze_root(
                            machine, bits, support, lower
                        )
                        if records is None:
                            row["terminal_contexts"] += 1
                            continue
                        row["open_contexts"] += 1
                        for record in records:
                            row["rank_group_checks"] += 1
                            row["max_frontier"] = max(
                                row["max_frontier"], int(record["frontier_card"])
                            )
                            if record["frontier_card"] == record["candidate_union_card"]:
                                row["tight_union_groups"] += 1
                            digest.update(json.dumps(record, sort_keys=True).encode())
                            digest.update(b"\n")
                        if failure is not None and first_failure is None:
                            first_failure = failure
                            row["block_expansion_failures"] += 1
                            if stop_on_failure:
                                stopped = True
                                break
                    if stopped:
                        break
                if stopped:
                    break
            if stopped:
                break
        by_size[str(size)] = row
        totals.update(row)
        if stopped:
            break

    return {
        "maximum_n": maximum_n,
        "strong_size": 6,
        "stop_on_failure": stop_on_failure,
        "stopped_early": stopped,
        "complete": not stopped,
        "statistics": {
            "totals": dict(sorted(totals.items())),
            "by_support_size": {
                size: dict(sorted(row.items())) for size, row in by_size.items()
            },
            "analyzed_local_states": len(machine.analysis_cache),
        },
        "first_block_failure": first_failure,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def replay(manifest: dict[str, object]) -> dict[str, object]:
    expected_k6 = manifest["k6_census"]
    frozen = frozen_gate()
    k6 = None
    if frozen["consecutive_block_expansion"] and expected_k6 is not None:
        k6 = k6_gate(
            int(expected_k6["maximum_n"]),
            bool(expected_k6["stop_on_failure"]),
        )
    return {"frozen_n12_k7": frozen, "k6_census": k6}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported manifest schema")
    repo = Path(__file__).resolve().parent.parent
    source_checks = {
        label: file_sha256(repo / metadata["path"]) == metadata["sha256"]
        for label, metadata in manifest["sources"].items()
    }
    checks: dict[str, bool] = {"sources": all(source_checks.values())}
    if not args.source_only:
        actual = replay(manifest)
        checks["frozen_n12_k7"] = (
            actual["frozen_n12_k7"] == manifest["frozen_n12_k7"]
        )
        checks["k6_census"] = actual["k6_census"] == manifest["k6_census"]
    print(json.dumps({"checks": checks, "source_checks": source_checks}, sort_keys=True))
    if not all(checks.values()):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
