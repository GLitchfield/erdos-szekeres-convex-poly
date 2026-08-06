#!/usr/bin/env python3
"""Exhaust the local Pascal-demand frontier at every decomposable root.

For every recursively deep-below coloring on every support of size at most
maximum_n, this producer visits every compatible root split. A crossing
endpoint pair is therefore a possible span allocated to that root as its
lowest separating node. For each color and exact local span rank, the gate
retains the two-sided interval frontier and compares its size with
choose(k - 2, rank - 1).

This is bounded computational evidence, not a Lean proof of the general
frontier bound. The independent checker imports none of this module.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import os
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

from enumerate_singleton_residuals import (
    DecomposableColorings,
    nonempty_proper_submasks,
)


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_revision(repo: Path) -> str:
    completed = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return completed.stdout.strip()


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def nondominated_intervals(pairs: list[tuple[int, int]]) -> tuple[tuple[int, int], ...]:
    """Keep intervals containing no distinct candidate interval."""
    return tuple(
        (left, right)
        for left, right in sorted(pairs)
        if not any(
            (left, right) != (other_left, other_right)
            and left <= other_left
            and other_right <= right
            for other_left, other_right in pairs
        )
    )


class LocalSpanAnalysis:
    def __init__(self, maximum_n: int, strong_size: int):
        self.maximum_n = maximum_n
        self.strong_size = strong_size
        self.triples = tuple(itertools.combinations(range(maximum_n), 3))
        self.positions = {triple: index for index, triple in enumerate(self.triples)}
        self.cache: dict[
            tuple[int, int], None | dict[tuple[int, int, int], int]
        ] = {}

    def color(self, bits: int, triple: tuple[int, int, int]) -> bool:
        return bool(bits & (1 << self.positions[triple]))

    def contains_strong(self, bits: int, support: int) -> bool:
        if support.bit_count() < self.strong_size:
            return False
        vertices = tuple(
            vertex
            for vertex in range(self.maximum_n)
            if support & (1 << vertex)
        )
        for chosen in itertools.combinations(vertices, self.strong_size):
            if all(
                self.color(bits, (a, b, c)) == self.color(bits, (a, b, d))
                and self.color(bits, (a, c, d)) == self.color(bits, (b, c, d))
                for a, b, c, d in itertools.combinations(chosen, 4)
            ):
                return True
        return False

    def analyze(
        self, bits: int, support: int
    ) -> None | dict[tuple[int, int, int], int]:
        key = support, bits
        if key in self.cache:
            return self.cache[key]
        if self.contains_strong(bits, support):
            self.cache[key] = None
            return None
        vertices = tuple(
            vertex
            for vertex in range(self.maximum_n)
            if support & (1 << vertex)
        )
        answer: dict[tuple[int, int, int], int] = {}
        for left, right in itertools.combinations(vertices, 2):
            interior = tuple(vertex for vertex in vertices if left < vertex < right)
            for color in (0, 1):
                rank = 2
                for size in range(
                    min(self.strong_size - 1, len(interior) + 2), 2, -1
                ):
                    found = False
                    for middle in itertools.combinations(interior, size - 2):
                        chain = (left, *middle, right)
                        if all(
                            self.color(bits, triple) == bool(color)
                            for triple in itertools.combinations(chain, 3)
                        ):
                            found = True
                            break
                    if found:
                        rank = size
                        break
                answer[color, left, right] = rank
        self.cache[key] = answer
        return answer


def context_groups(
    local: dict[tuple[int, int, int], int],
    support: int,
    lower: int,
    maximum_n: int,
) -> tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...]:
    vertices = tuple(
        vertex for vertex in range(maximum_n) if support & (1 << vertex)
    )
    grouped: defaultdict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    for left, right in itertools.combinations(vertices, 2):
        if bool(lower & (1 << left)) == bool(lower & (1 << right)):
            continue
        for color in (0, 1):
            rank = local[color, left, right]
            if rank >= 3:
                grouped[color, rank].append((left, right))
    return tuple(
        (color, rank, nondominated_intervals(pairs))
        for (color, rank), pairs in sorted(grouped.items())
    )


def contains_monochromatic_subset(
    analyzer: LocalSpanAnalysis,
    bits: int,
    vertices: tuple[int, ...],
    color: int,
    size: int,
) -> bool:
    """Test one cup--cap outcome directly on a projected endpoint set."""
    if size > len(vertices):
        return False
    return any(
        all(
            analyzer.color(bits, triple) == bool(color)
            for triple in itertools.combinations(chosen, 3)
        )
        for chosen in itertools.combinations(vertices, size)
    )


def endpoint_projection_supports_pascal_shortcut(
    analyzer: LocalSpanAnalysis,
    bits: int,
    vertices: tuple[int, ...],
    color: int,
    rank: int,
) -> bool:
    """Whether the classical cup--cap theorem applies to this projection."""
    return not contains_monochromatic_subset(
        analyzer, bits, vertices, color, rank + 1
    ) and not contains_monochromatic_subset(
        analyzer,
        bits,
        vertices,
        1 - color,
        analyzer.strong_size + 1 - rank,
    )


def endpoint_rank_ideal(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    endpoint: int,
    color: int,
    rank: int,
    strong_size: int,
    incoming: bool,
) -> int:
    """Encode the truncated same/opposite pair-rank lower ideal."""
    rows = rank - 1
    columns = strong_size - rank - 1
    answer = 0
    for row in range(rows):
        for column in range(columns):
            same_threshold = row + 2
            opposite_threshold = column + 2
            witnessed = any(
                (
                    vertex < endpoint
                    and local[color, vertex, endpoint] >= same_threshold
                    and local[1 - color, vertex, endpoint] >= opposite_threshold
                )
                if incoming
                else (
                    endpoint < vertex
                    and local[color, endpoint, vertex] >= same_threshold
                    and local[1 - color, endpoint, vertex] >= opposite_threshold
                )
                for vertex in vertices
            )
            if witnessed:
                answer |= 1 << (row * columns + column)
    return answer


def rectangular_lower_ideals(rows: int, columns: int) -> tuple[int, ...]:
    """Enumerate all lower ideals independently of binomial arithmetic."""
    answer = []
    for mask in range(1 << (rows * columns)):
        valid = True
        for row in range(rows):
            for column in range(columns):
                position = row * columns + column
                if not mask & (1 << position):
                    continue
                if row and not mask & (1 << (position - columns)):
                    valid = False
                if column and not mask & (1 << (position - 1)):
                    valid = False
        if valid:
            answer.append(mask)
    return tuple(answer)


def ideal_interval(
    ideals: tuple[int, ...], first: int, second: int
) -> tuple[int, ...]:
    """The lattice interval from meet to join of two ideals."""
    lower = first & second
    upper = first | second
    return tuple(
        ideal
        for ideal in ideals
        if ideal & lower == lower and ideal | upper == upper
    )


def has_distinct_representatives(
    candidates: tuple[tuple[int, ...], ...]
) -> bool:
    """Bipartite augmenting-path test for Hall representatives."""
    matched: dict[int, int] = {}

    def augment(span: int, seen: set[int]) -> bool:
        for ideal in candidates[span]:
            if ideal in seen:
                continue
            seen.add(ideal)
            if ideal not in matched or augment(matched[ideal], seen):
                matched[ideal] = span
                return True
        return False

    return all(augment(span, set()) for span in range(len(candidates)))


def endpoint_transition_candidates(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    frontier: tuple[tuple[int, int], ...],
    color: int,
    rank: int,
    strong_size: int,
) -> tuple[
    tuple[tuple[int, ...], ...],
    tuple[tuple[int, ...], ...],
    tuple[tuple[int, ...], ...],
    tuple[tuple[int, ...], ...],
]:
    """Return two-way, left-only, right-only, and fixed-four candidates."""
    ideals = rectangular_lower_ideals(rank - 1, strong_size - rank - 1)
    two_way = []
    left_only = []
    right_only = []
    fixed_four = []
    for left, right in frontier:
        endpoint_intervals = []
        fixed = set()
        for endpoint in (left, right):
            past = endpoint_rank_ideal(
                local, vertices, endpoint, color, rank, strong_size, True
            )
            future = endpoint_rank_ideal(
                local, vertices, endpoint, color, rank, strong_size, False
            )
            endpoint_intervals.append(ideal_interval(ideals, past, future))
            fixed.update((past, future))
        left_only.append(endpoint_intervals[0])
        right_only.append(endpoint_intervals[1])
        two_way.append(
            tuple(sorted(set(endpoint_intervals[0]) | set(endpoint_intervals[1])))
        )
        fixed_four.append(tuple(sorted(fixed)))
    return tuple(two_way), tuple(left_only), tuple(right_only), tuple(fixed_four)


def digest_context(
    digest,
    support: int,
    lower: int,
    bits: int,
    groups: None | tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...],
) -> None:
    if groups is None:
        record = ["terminal", support, lower, bits]
    else:
        record = [
            "open",
            support,
            lower,
            bits,
            [
                [color, rank, [[left, right] for left, right in frontier]]
                for color, rank, frontier in groups
            ],
        ]
    digest.update(json.dumps(record, separators=(",", ":")).encode())
    digest.update(b"\n")


def example(
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


def produce(maximum_n: int, strong_size: int) -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_allocated_span_pascal_demand.py"
    colorings = DecomposableColorings(maximum_n)
    colorings.enumerate()
    analyzer = LocalSpanAnalysis(maximum_n, strong_size)

    totals: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    rank_rows: dict[tuple[int, int], Counter[str]] = {}
    projection_rows: dict[tuple[int, int], Counter[str]] = {}
    transition_rows: dict[tuple[int, int], Counter[str]] = {}
    projection_examples: dict[tuple[int, int], dict[str, object]] = {}
    transition_failure = None
    fixed_failure_examples: dict[tuple[int, int], dict[str, object]] = {}
    saturation_examples: dict[tuple[int, int], dict[str, object]] = {}
    violation = None
    digest = hashlib.sha256()

    for size in range(2, maximum_n + 1):
        row: Counter[str] = Counter()
        for support in range(1, 1 << maximum_n):
            if support.bit_count() != size:
                continue
            vertices = tuple(
                vertex
                for vertex in range(maximum_n)
                if support & (1 << vertex)
            )
            for lower in nonempty_proper_submasks(support):
                upper = support ^ lower
                fixed = colorings.crossing_bits(support, lower)
                seen: set[int] = set()
                for lower_bits in sorted(colorings.states[lower]):
                    for upper_bits in sorted(colorings.states[upper]):
                        bits = lower_bits | upper_bits | fixed
                        if bits in seen:
                            raise AssertionError(
                                "child restrictions failed to identify a root context"
                            )
                        seen.add(bits)
                        row["root_contexts"] += 1
                        local = analyzer.analyze(bits, support)
                        if local is None:
                            row["terminal_contexts"] += 1
                            digest_context(digest, support, lower, bits, None)
                            continue
                        row["open_contexts"] += 1
                        groups = context_groups(local, support, lower, maximum_n)
                        digest_context(digest, support, lower, bits, groups)
                        for color, rank, frontier in groups:
                            row["rank_group_checks"] += 1
                            key = color, rank
                            rank_row = rank_rows.setdefault(key, Counter())
                            capacity = math.comb(strong_size - 2, rank - 1)
                            rank_row["group_count"] += 1
                            rank_row["max_frontier"] = max(
                                rank_row["max_frontier"], len(frontier)
                            )
                            if len(frontier) == capacity:
                                rank_row["saturation_count"] += 1
                                saturation_examples.setdefault(
                                    key, example(support, lower, bits, frontier)
                                )
                            if len(frontier) > capacity:
                                row["violations"] += 1
                                if violation is None:
                                    violation = {
                                        **example(support, lower, bits, frontier),
                                        "color": "cup" if color else "cap",
                                        "rank": rank,
                                        "capacity": capacity,
                                    }
                            projection_row = projection_rows.setdefault(
                                key, Counter()
                            )
                            projection_row["group_count"] += 1
                            left_endpoints = tuple(left for left, _ in frontier)
                            right_endpoints = tuple(right for _, right in frontier)
                            left_ok = endpoint_projection_supports_pascal_shortcut(
                                analyzer, bits, left_endpoints, color, rank
                            )
                            right_ok = endpoint_projection_supports_pascal_shortcut(
                                analyzer, bits, right_endpoints, color, rank
                            )
                            if not left_ok:
                                projection_row["left_failures"] += 1
                            if not right_ok:
                                projection_row["right_failures"] += 1
                            if not left_ok and not right_ok:
                                projection_row["both_failures"] += 1
                                projection_examples.setdefault(
                                    key,
                                    {
                                        **example(support, lower, bits, frontier),
                                        "left_endpoints": list(left_endpoints),
                                        "right_endpoints": list(right_endpoints),
                                    },
                                )
                            transition_row = transition_rows.setdefault(
                                key, Counter()
                            )
                            transition_row["group_count"] += 1
                            (
                                two_way,
                                left_intervals,
                                right_intervals,
                                fixed_four,
                            ) = endpoint_transition_candidates(
                                local,
                                vertices,
                                frontier,
                                color,
                                rank,
                                strong_size,
                            )
                            if not has_distinct_representatives(left_intervals):
                                transition_row["left_only_failures"] += 1
                            if not has_distinct_representatives(right_intervals):
                                transition_row["right_only_failures"] += 1
                            if not has_distinct_representatives(fixed_four):
                                transition_row["fixed_four_failures"] += 1
                                fixed_failure_examples.setdefault(
                                    key,
                                    {
                                        **example(
                                            support, lower, bits, frontier
                                        ),
                                        "candidate_ideals_hex": [
                                            [f"{ideal:x}" for ideal in candidates]
                                            for candidates in fixed_four
                                        ],
                                    },
                                )
                            if not has_distinct_representatives(two_way):
                                transition_row["two_way_failures"] += 1
                                if transition_failure is None:
                                    transition_failure = {
                                        **example(
                                            support, lower, bits, frontier
                                        ),
                                        "color": "cup" if color else "cap",
                                        "rank": rank,
                                        "candidate_ideals_hex": [
                                            [f"{ideal:x}" for ideal in candidates]
                                            for candidates in two_way
                                        ],
                                    }
        by_size[str(size)] = row
        totals.update(row)

    rank_census = {}
    for (color, rank), row in sorted(rank_rows.items()):
        capacity = math.comb(strong_size - 2, rank - 1)
        rank_census[f"{'cup' if color else 'cap'},{rank}"] = {
            "capacity": capacity,
            "group_count": row["group_count"],
            "max_frontier": row["max_frontier"],
            "minimum_observed_slack": capacity - row["max_frontier"],
            "saturation_count": row["saturation_count"],
        }
    examples = {
        f"{'cup' if color else 'cap'},{rank}": value
        for (color, rank), value in sorted(saturation_examples.items())
    }
    projection_census = {
        f"{'cup' if color else 'cap'},{rank}": dict(sorted(row.items()))
        for (color, rank), row in sorted(projection_rows.items())
    }
    projection_failure_examples = {
        f"{'cup' if color else 'cap'},{rank}": value
        for (color, rank), value in sorted(projection_examples.items())
    }
    transition_census = {
        f"{'cup' if color else 'cap'},{rank}": dict(sorted(row.items()))
        for (color, rank), row in sorted(transition_rows.items())
    }
    fixed_transition_failure_examples = {
        f"{'cup' if color else 'cap'},{rank}": value
        for (color, rank), value in sorted(fixed_failure_examples.items())
    }
    return {
        "schema_version": 1,
        "experiment": "allocated-span-pascal-demand-frontier",
        "generation_base_revision": git_revision(repo),
        "parameters": {
            "maximum_n": maximum_n,
            "strong_size": strong_size,
            "minimum_recorded_rank": 3,
        },
        "contract": {
            "contexts": (
                "every recursively deep-below coloring on every labeled support "
                "and every compatible nontrivial root split"
            ),
            "allocation": (
                "a crossing endpoint pair is allocated to the current root, "
                "representing its unique lowest separating node"
            ),
            "rank": (
                "maximum local monochromatic cup/cap chain size with the exact "
                "ordered endpoint pair; terminal strong-k contexts are skipped"
            ),
            "frontier": (
                "fixed-color fixed-exact-rank intervals containing no distinct "
                "candidate interval"
            ),
            "capacity": "Nat.choose (k - 2) (rank - 1)",
            "endpoint_transition_hall": (
                "for each retained span and each endpoint, encode the past "
                "and future predecessor/successor rank incidences as lower "
                "ideals of the truncated (rank-1)-by-(k-rank-1) Pascal grid; "
                "the span may use any ideal between meet and join at either "
                "endpoint, and the tested claim is that all spans admit "
                "distinct representatives from those two interval unions"
            ),
            "endpoint_projection_shortcut": (
                "the left or right endpoint set would support the direct "
                "classical cup--cap reduction only if it avoids a color-rank+1 "
                "chain and an opposite-color-(k+1-rank) chain"
            ),
            "claim_boundary": (
                "The census is bounded evidence only; it neither proves the "
                "general frontier bound nor supplies a global injective charge."
            ),
        },
        "statistics": {
            "totals": dict(sorted(totals.items())),
            "by_support_size": {
                size: dict(sorted(row.items())) for size, row in by_size.items()
            },
            "analyzed_local_states": len(analyzer.cache),
        },
        "rank_census": rank_census,
        "endpoint_projection_falsifier": {
            "census": projection_census,
            "first_both_failure_examples": projection_failure_examples,
        },
        "endpoint_transition_hall_gate": {
            "census": transition_census,
            "first_fixed_four_failure_examples": fixed_transition_failure_examples,
            "first_two_way_failure": transition_failure,
        },
        "first_saturation_examples": examples,
        "first_violation": violation,
        "canonical_context_sha256": digest.hexdigest(),
        "observed_claim": (
            "Every tested exact-rank two-sided interval frontier fits its "
            "adjacent Pascal demand and admits distinct representatives from "
            "the two-endpoint transition-ideal candidate sets."
        ),
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-n", type=int, default=8)
    parser.add_argument("--strong-size", type=int, default=6)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 2 <= args.maximum_n <= 8:
        parser.error("--maximum-n must lie between 2 and 8")
    if not 4 <= args.strong_size <= 15:
        parser.error("--strong-size must lie between 4 and 15")
    write_atomic(args.output, produce(args.maximum_n, args.strong_size))
    print(args.output)


if __name__ == "__main__":
    main()
