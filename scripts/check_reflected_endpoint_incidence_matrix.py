#!/usr/bin/env python3
"""Produce the frozen reflected endpoint-incidence matrix gate.

Rows are retained exact-rank spans and columns are the existing untagged
rectangular lower ideals.  An entry counts how many of the span's two
orientation-reflected endpoint intervals contain the ideal, so it lies in
{0, 1, 2}.  Exact rational row reduction tests the proposed independence
mechanism and records every inclusion-minimal row dependency.
"""

from __future__ import annotations

import argparse
import itertools
import math
from fractions import Fraction
from pathlib import Path

from enumerate_allocated_span_pascal_demand import (
    DecomposableColorings,
    LocalSpanAnalysis,
    context_groups,
    endpoint_transition_candidates,
    file_sha256,
    git_revision,
    rectangular_lower_ideals,
    write_atomic,
)
from enumerate_reflected_transition_hall import (
    FROZEN_LOWER_TREE,
    FROZEN_TREE,
    reflected_ideal,
    tree_coloring_bits,
    tree_support,
)


def rational_rank(rows: tuple[tuple[int, ...], ...]) -> int:
    """Rank over Q by deterministic reduced row echelon elimination."""
    if not rows:
        return 0
    matrix = [[Fraction(value) for value in row] for row in rows]
    pivot_row = 0
    for column in range(len(matrix[0])):
        pivot = next(
            (row for row in range(pivot_row, len(matrix)) if matrix[row][column]),
            None,
        )
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        scale = matrix[pivot_row][column]
        matrix[pivot_row] = [value / scale for value in matrix[pivot_row]]
        for row in range(len(matrix)):
            if row == pivot_row or not matrix[row][column]:
                continue
            factor = matrix[row][column]
            matrix[row] = [
                value - factor * pivot_value
                for value, pivot_value in zip(
                    matrix[row], matrix[pivot_row], strict=True
                )
            ]
        pivot_row += 1
        if pivot_row == len(matrix):
            break
    return pivot_row


def primitive_relation(rows: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    """Return the normalized unique dependency of a circuit of rows."""
    variables = len(rows)
    equations = len(rows[0]) if rows else 0
    matrix = [
        [Fraction(rows[variable][equation]) for variable in range(variables)]
        for equation in range(equations)
    ]
    pivot_columns: list[int] = []
    pivot_row = 0
    for column in range(variables):
        pivot = next(
            (row for row in range(pivot_row, equations) if matrix[row][column]),
            None,
        )
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        scale = matrix[pivot_row][column]
        matrix[pivot_row] = [value / scale for value in matrix[pivot_row]]
        for row in range(equations):
            if row == pivot_row or not matrix[row][column]:
                continue
            factor = matrix[row][column]
            matrix[row] = [
                value - factor * pivot_value
                for value, pivot_value in zip(
                    matrix[row], matrix[pivot_row], strict=True
                )
            ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == equations:
            break
    free = [column for column in range(variables) if column not in pivot_columns]
    if len(free) != 1:
        raise AssertionError("a minimal dependent row family must have nullity one")
    answer = [Fraction(0) for _ in range(variables)]
    answer[free[0]] = 1
    for row, column in reversed(list(enumerate(pivot_columns))):
        answer[column] = -sum(
            matrix[row][other] * answer[other]
            for other in range(column + 1, variables)
        )
    common_denominator = math.lcm(*(value.denominator for value in answer))
    integers = [int(value * common_denominator) for value in answer]
    common_divisor = math.gcd(*(abs(value) for value in integers))
    integers = [value // common_divisor for value in integers]
    first = next(value for value in integers if value)
    if first < 0:
        integers = [-value for value in integers]
    relation = tuple(integers)
    if any(
        sum(coefficient * row[column] for coefficient, row in zip(relation, rows))
        for column in range(equations)
    ):
        raise AssertionError("computed circuit vector is not a row dependency")
    return relation


def row_circuits(rows: tuple[tuple[int, ...], ...]) -> list[dict[str, object]]:
    circuits = []
    for size in range(1, len(rows) + 1):
        for indices in itertools.combinations(range(len(rows)), size):
            selected = tuple(rows[index] for index in indices)
            if rational_rank(selected) == size:
                continue
            if any(
                rational_rank(selected[:offset] + selected[offset + 1 :])
                != size - 1
                for offset in range(size)
            ):
                continue
            circuits.append(
                {
                    "row_indices": list(indices),
                    "coefficients": list(primitive_relation(selected)),
                }
            )
    return circuits


def oriented_interval(
    family: tuple[int, ...],
    reflect: bool,
    rows: int,
    columns: int,
) -> tuple[int, ...]:
    if not reflect:
        return family
    return tuple(sorted(reflected_ideal(ideal, rows, columns) for ideal in family))


def group_record(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    frontier: tuple[tuple[int, int], ...],
    lower: int,
    color: int,
    rank: int,
    strong_size: int,
) -> dict[str, object]:
    rows = rank - 1
    columns = strong_size - rank - 1
    ideals = rectangular_lower_ideals(rows, columns)
    _, left_intervals, right_intervals, _ = endpoint_transition_candidates(
        local, vertices, frontier, color, rank, strong_size
    )
    oriented_pairs = []
    matrix = []
    for span, left_family, right_family in zip(
        frontier, left_intervals, right_intervals, strict=True
    ):
        reflect = not bool(lower & (1 << span[0]))
        oriented_left = oriented_interval(left_family, reflect, rows, columns)
        oriented_right = oriented_interval(right_family, reflect, rows, columns)
        oriented_pairs.append((oriented_left, oriented_right))
        matrix.append(
            tuple(
                int(ideal in oriented_left) + int(ideal in oriented_right)
                for ideal in ideals
            )
        )
    matrix_rows = tuple(matrix)
    rank_q = rational_rank(matrix_rows)
    circuits = row_circuits(matrix_rows)
    for circuit in circuits:
        circuit["spans"] = [
            list(frontier[index]) for index in circuit["row_indices"]
        ]
    return {
        "color": "cup" if color else "cap",
        "rank": rank,
        "grid_rows": rows,
        "grid_columns": columns,
        "frontier": [list(span) for span in frontier],
        "ideal_columns_hex": [f"{ideal:x}" for ideal in ideals],
        "oriented_endpoint_intervals_hex": [
            {
                "left": [f"{ideal:x}" for ideal in left_family],
                "right": [f"{ideal:x}" for ideal in right_family],
            }
            for left_family, right_family in oriented_pairs
        ],
        "incidence_matrix": [list(row) for row in matrix_rows],
        "rational_row_rank": rank_q,
        "full_row_rank": rank_q == len(frontier),
        "row_circuits": circuits,
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
    vertices = tuple(
        vertex for vertex in range(maximum_n) if support & (1 << vertex)
    )
    groups = [
        group_record(
            local, vertices, frontier, lower, color, rank, strong_size
        )
        for color, rank, frontier in context_groups(
            local, support, lower, maximum_n
        )
    ]
    first_failure = next(
        (index for index, group in enumerate(groups) if not group["full_row_rank"]),
        None,
    )
    return {
        "maximum_n": maximum_n,
        "strong_size": strong_size,
        "support_mask_hex": f"{support:x}",
        "lower_mask_hex": f"{lower:x}",
        "coloring_hex": f"{bits:x}",
        "rank_group_checks": len(groups),
        "groups": groups,
        "all_groups_full_row_rank": first_failure is None,
        "first_rank_deficient_group": first_failure,
    }


def produce(repo: Path) -> dict[str, object]:
    producer = Path(__file__).resolve()
    checker = repo / "scripts/replay_reflected_endpoint_incidence_matrix.py"
    return {
        "schema_version": 1,
        "experiment": "frozen-reflected-endpoint-incidence-matrix-gate",
        "generation_base_revision": git_revision(repo),
        "contract": {
            "columns": "existing untagged rectangular lower ideals",
            "rows": "retained exact-rank frontier spans in endpoint order",
            "entry": (
                "number in {0,1,2} of the two orientation-reflected endpoint "
                "intervals containing the ideal"
            ),
            "failure": (
                "any exact rational row-rank defect refutes this linear-"
                "independence mechanism only"
            ),
            "claim_boundary": "bounded frozen-root computation, not a Lean theorem",
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
