#!/usr/bin/env python3
"""Independently replay orientation-reflected transition-Hall gates.

This checker imports no code from the reflected-gate producer.  It represents
rectangular ideals by nonincreasing row heights, uses the existing independent
decomposable-coloring replay, and tests representatives by backtracking.
"""

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


def reflected_heights(
    ideal: tuple[int, ...], columns: int
) -> tuple[int, ...]:
    """Rotate-complement an ideal represented by row heights."""
    return tuple(columns - height for height in reversed(ideal))


def oriented_candidates(
    candidates: tuple[tuple[tuple[int, ...], ...], ...],
    frontier: tuple[tuple[int, int], ...],
    lower: int,
    columns: int,
) -> tuple[tuple[tuple[int, ...], ...], ...]:
    answer = []
    for family, (left, _) in zip(candidates, frontier, strict=True):
        if lower & (1 << left):
            answer.append(family)
        else:
            answer.append(
                tuple(
                    sorted(
                        (reflected_heights(ideal, columns) for ideal in family),
                        key=lambda ideal: int(height_mask_hex(ideal, columns), 16),
                    )
                )
            )
    return tuple(answer)


def candidate_hex(
    candidates: tuple[tuple[tuple[int, ...], ...], ...], columns: int
) -> list[list[str]]:
    return [
        [height_mask_hex(ideal, columns) for ideal in family]
        for family in candidates
    ]


def reflected_mask(mask: int, rows: int, columns: int) -> int:
    answer = 0
    for target in range(rows * columns):
        row, column = divmod(target, columns)
        source = (rows - 1 - row) * columns + (columns - 1 - column)
        if not mask & (1 << source):
            answer |= 1 << target
    return answer


def rigid_obstructions(
    original_hex: list[list[str]],
    oriented_hex: list[list[str]],
    frontier: tuple[tuple[int, int], ...],
    lower: int,
    rows: int,
    columns: int,
) -> dict[str, object]:
    original = tuple(tuple(int(value, 16) for value in family) for family in original_hex)
    oriented = tuple(tuple(int(value, 16) for value in family) for family in oriented_hex)
    rigid = [index for index, family in enumerate(oriented) if len(family) == 1]
    same_orientation = None
    fixed_opposite = None
    opposite = None
    by_label: dict[int, list[int]] = {}
    for index in rigid:
        by_label.setdefault(oriented[index][0], []).append(index)
    triple = next(
        (indices[:3] for indices in by_label.values() if len(indices) >= 3), None
    )
    for offset, first in enumerate(rigid):
        for second in rigid[offset + 1 :]:
            if oriented[first][0] != oriented[second][0]:
                continue
            first_lower = bool(lower & (1 << frontier[first][0]))
            second_lower = bool(lower & (1 << frontier[second][0]))
            if first_lower == second_lower and same_orientation is None:
                same_orientation = [first, second]
            if first_lower != second_lower and opposite is None:
                opposite = [first, second]
            if (
                first_lower != second_lower
                and len(original[first]) == 1
                and len(original[second]) == 1
                and original[first][0] == original[second][0]
                and reflected_mask(original[first][0], rows, columns)
                == original[first][0]
                and fixed_opposite is None
            ):
                fixed_opposite = [first, second]
    return {
        "same_orientation_rigid_pair": same_orientation,
        "opposite_orientation_rigid_pair": opposite,
        "reflection_fixed_opposite_pair": fixed_opposite,
        "triple_rigid_collision": triple,
    }


def make_example(
    support: int,
    lower: int,
    bits: int,
    frontier: tuple[tuple[int, int], ...],
) -> dict[str, object]:
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "frontier": [list(pair) for pair in frontier],
    }


def group_record(
    support: int,
    lower: int,
    bits: int,
    color: int,
    rank: int,
    frontier: tuple[tuple[int, int], ...],
    original: tuple[tuple[tuple[int, ...], ...], ...],
    oriented: tuple[tuple[tuple[int, ...], ...], ...],
    strong_size: int,
) -> dict[str, object]:
    rows = rank - 1
    columns = strong_size - rank - 1
    original_hex = candidate_hex(original, columns)
    oriented_hex = candidate_hex(oriented, columns)
    return {
        **make_example(support, lower, bits, frontier),
        "color": "cup" if color else "cap",
        "rank": rank,
        "rows": rows,
        "columns": columns,
        "original_candidates_hex": original_hex,
        "oriented_candidates_hex": oriented_hex,
        "rigid_obstructions": rigid_obstructions(
            original_hex, oriented_hex, frontier, lower, rows, columns
        ),
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
        original, _, _, _ = replay_transition_candidates(
            local, vertices, frontier, color, rank, machine.strong_size
        )
        columns = machine.strong_size - rank - 1
        oriented = oriented_candidates(original, frontier, lower, columns)
        record = group_record(
            support,
            lower,
            bits,
            color,
            rank,
            frontier,
            original,
            oriented,
            machine.strong_size,
        )
        record["hall"] = replay_distinct_representatives(oriented)
        records.append(record)
        if not record["hall"] and first_failure is None:
            first_failure = record
    return records, first_failure


def frozen_gate() -> dict[str, object]:
    machine = Replay(12, 7)
    support = tree_support(FROZEN_TREE)
    lower = tree_support(FROZEN_LOWER_TREE)
    bits = tree_coloring_bits(FROZEN_TREE, machine)
    records, first_failure = analyze_root(machine, bits, support, lower)
    if records is None:
        raise AssertionError("frozen collision unexpectedly contains a strong seven")
    target = next(
        record
        for record in records
        if record["color"] == "cap"
        and record["rank"] == 3
        and [4, 6] in record["frontier"]
        and [5, 7] in record["frontier"]
    )
    first_index = target["frontier"].index([4, 6])
    second_index = target["frontier"].index([5, 7])
    return {
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "rank_group_checks": len(records),
        "target_pair": {
            "first": [4, 6],
            "second": [5, 7],
            "first_original_hex": target["original_candidates_hex"][first_index],
            "second_original_hex": target["original_candidates_hex"][second_index],
            "first_oriented_hex": target["oriented_candidates_hex"][first_index],
            "second_oriented_hex": target["oriented_candidates_hex"][second_index],
            "pair_separated": (
                target["oriented_candidates_hex"][first_index]
                != target["oriented_candidates_hex"][second_index]
            ),
        },
        "full_frontier_hall": first_failure is None,
        "first_hall_failure": first_failure,
    }


def k6_gate(maximum_n: int, stop_on_failure: bool) -> dict[str, object]:
    machine = Replay(maximum_n, 6)
    full = (1 << maximum_n) - 1
    machine.colorings(full)
    counts: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    first_failure = None
    first_targeted: dict[str, dict[str, object]] = {}
    digest = hashlib.sha256()
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
                            digest.update(
                                json.dumps(record, sort_keys=True).encode()
                            )
                            digest.update(b"\n")
                            for label, witness in record[
                                "rigid_obstructions"
                            ].items():
                                if witness is not None:
                                    row[label] += 1
                                    first_targeted.setdefault(label, record)
                        if failure is not None and first_failure is None:
                            first_failure = failure
                            row["hall_failures"] += 1
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
        counts.update(row)
        if stopped:
            break

    return {
        "maximum_n": maximum_n,
        "strong_size": 6,
        "stop_on_failure": stop_on_failure,
        "stopped_early": stopped,
        "complete": not stopped,
        "statistics": {
            "totals": dict(sorted(counts.items())),
            "by_support_size": {
                size: dict(sorted(row.items())) for size, row in by_size.items()
            },
            "analyzed_local_states": len(machine.analysis_cache),
        },
        "first_targeted_obstructions": dict(sorted(first_targeted.items())),
        "first_hall_failure": first_failure,
        "checked_prefix_sha256": digest.hexdigest(),
    }


def replay(manifest: dict[str, object]) -> dict[str, object]:
    expected_k6 = manifest["k6_census"]
    frozen = frozen_gate()
    k6 = None
    if frozen["full_frontier_hall"] and expected_k6 is not None:
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
