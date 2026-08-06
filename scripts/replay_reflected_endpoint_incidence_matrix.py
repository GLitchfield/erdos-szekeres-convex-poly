#!/usr/bin/env python3
"""Independently replay the frozen reflected endpoint-incidence matrices."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path

from check_allocated_span_pascal_demand import (
    Replay,
    file_sha256,
    groups,
    height_ideals,
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


def reflected_heights(
    ideal: tuple[int, ...], columns: int
) -> tuple[int, ...]:
    return tuple(columns - height for height in reversed(ideal))


def determinant(matrix: tuple[tuple[int, ...], ...]) -> int:
    """Fraction-free Bareiss determinant."""
    size = len(matrix)
    if size == 0:
        return 1
    work = [list(row) for row in matrix]
    sign = 1
    previous = 1
    for pivot_index in range(size - 1):
        pivot_row = next(
            (row for row in range(pivot_index, size) if work[row][pivot_index]),
            None,
        )
        if pivot_row is None:
            return 0
        if pivot_row != pivot_index:
            work[pivot_index], work[pivot_row] = work[pivot_row], work[pivot_index]
            sign = -sign
        pivot = work[pivot_index][pivot_index]
        for row in range(pivot_index + 1, size):
            for column in range(pivot_index + 1, size):
                numerator = (
                    work[row][column] * pivot
                    - work[row][pivot_index] * work[pivot_index][column]
                )
                if numerator % previous:
                    raise AssertionError("Bareiss division was not exact")
                work[row][column] = numerator // previous
        previous = pivot
    return sign * work[-1][-1]


def integer_rank(rows: tuple[tuple[int, ...], ...]) -> int:
    if not rows:
        return 0
    row_count = len(rows)
    column_count = len(rows[0])
    for size in range(min(row_count, column_count), 0, -1):
        for row_indices in itertools.combinations(range(row_count), size):
            for column_indices in itertools.combinations(range(column_count), size):
                minor = tuple(
                    tuple(rows[row][column] for column in column_indices)
                    for row in row_indices
                )
                if determinant(minor):
                    return size
    return 0


def normalize(values: list[int]) -> tuple[int, ...]:
    divisor = math.gcd(*(abs(value) for value in values))
    values = [value // divisor for value in values]
    first = next(value for value in values if value)
    if first < 0:
        values = [-value for value in values]
    return tuple(values)


def cofactor_relation(rows: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    size = len(rows)
    for columns in itertools.combinations(range(len(rows[0])), size - 1):
        coefficients = []
        for omitted in range(size):
            minor = tuple(
                tuple(rows[row][column] for column in columns)
                for row in range(size)
                if row != omitted
            )
            coefficients.append((1 if omitted % 2 == 0 else -1) * determinant(minor))
        if any(coefficients):
            relation = normalize(coefficients)
            if any(
                sum(
                    coefficient * row[column]
                    for coefficient, row in zip(relation, rows, strict=True)
                )
                for column in range(len(rows[0]))
            ):
                raise AssertionError("cofactor vector is not a full row relation")
            return relation
    raise AssertionError("circuit has no rank-size-minus-one column minor")


def row_circuits(rows: tuple[tuple[int, ...], ...]) -> list[dict[str, object]]:
    answer = []
    for size in range(1, len(rows) + 1):
        for indices in itertools.combinations(range(len(rows)), size):
            selected = tuple(rows[index] for index in indices)
            if integer_rank(selected) == size:
                continue
            if any(
                integer_rank(selected[:offset] + selected[offset + 1 :])
                != size - 1
                for offset in range(size)
            ):
                continue
            answer.append(
                {
                    "row_indices": list(indices),
                    "coefficients": list(cofactor_relation(selected)),
                }
            )
    return answer


def group_record(
    local: dict[tuple[int, int, int], int],
    support_vertices: tuple[int, ...],
    frontier: tuple[tuple[int, int], ...],
    lower: int,
    color: int,
    rank: int,
    strong_size: int,
) -> dict[str, object]:
    grid_rows = rank - 1
    grid_columns = strong_size - rank - 1
    ideal_words = tuple(
        sorted(
            height_ideals(grid_rows, grid_columns),
            key=lambda ideal: int(height_mask_hex(ideal, grid_columns), 16),
        )
    )
    _, left_intervals, right_intervals, _ = replay_transition_candidates(
        local, support_vertices, frontier, color, rank, strong_size
    )
    pairs = []
    matrix = []
    for span, left_family, right_family in zip(
        frontier, left_intervals, right_intervals, strict=True
    ):
        reflect = not bool(lower & (1 << span[0]))
        if reflect:
            left_family = tuple(
                sorted(
                    (reflected_heights(ideal, grid_columns) for ideal in left_family),
                    key=lambda ideal: int(height_mask_hex(ideal, grid_columns), 16),
                )
            )
            right_family = tuple(
                sorted(
                    (reflected_heights(ideal, grid_columns) for ideal in right_family),
                    key=lambda ideal: int(height_mask_hex(ideal, grid_columns), 16),
                )
            )
        pairs.append((left_family, right_family))
        matrix.append(
            tuple(
                int(ideal in left_family) + int(ideal in right_family)
                for ideal in ideal_words
            )
        )
    matrix_rows = tuple(matrix)
    rank_z = integer_rank(matrix_rows)
    circuits = row_circuits(matrix_rows)
    for circuit in circuits:
        circuit["spans"] = [
            list(frontier[index]) for index in circuit["row_indices"]
        ]
    return {
        "color": "cup" if color else "cap",
        "rank": rank,
        "grid_rows": grid_rows,
        "grid_columns": grid_columns,
        "frontier": [list(span) for span in frontier],
        "ideal_columns_hex": [
            height_mask_hex(ideal, grid_columns) for ideal in ideal_words
        ],
        "oriented_endpoint_intervals_hex": [
            {
                "left": [height_mask_hex(ideal, grid_columns) for ideal in left_family],
                "right": [height_mask_hex(ideal, grid_columns) for ideal in right_family],
            }
            for left_family, right_family in pairs
        ],
        "incidence_matrix": [list(row) for row in matrix_rows],
        "rational_row_rank": rank_z,
        "full_row_rank": rank_z == len(frontier),
        "row_circuits": circuits,
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
    records = [
        group_record(
            local,
            support_vertices,
            frontier,
            lower,
            color,
            rank,
            strong_size,
        )
        for color, rank, frontier in groups(local, support, lower, maximum_n)
    ]
    first_failure = next(
        (index for index, group in enumerate(records) if not group["full_row_rank"]),
        None,
    )
    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "rank_group_checks": len(records),
        "groups": records,
        "all_groups_full_row_rank": first_failure is None,
        "first_rank_deficient_group": first_failure,
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
        raise AssertionError("independent endpoint-incidence replay differs")
    print(
        "all_groups_full_row_rank=",
        replay["all_groups_full_row_rank"],
        "ranks=",
        [group["rational_row_rank"] for group in replay["groups"]],
        "frontier_cards=",
        [len(group["frontier"]) for group in replay["groups"]],
        "circuits=",
        [len(group["row_circuits"]) for group in replay["groups"]],
    )


if __name__ == "__main__":
    main()
