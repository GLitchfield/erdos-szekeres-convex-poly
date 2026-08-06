#!/usr/bin/env python3
"""Independently replay the allocated span Pascal-demand frontier census.

This checker imports no producer module. It rebuilds decomposable colorings
with a recursive cache, computes exact local ranks directly from triple
colors, obtains interval frontiers by a descending-left scan, and computes
capacities with a Pascal table rather than math.comb.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
from collections import Counter, defaultdict
from pathlib import Path


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def proper_parts(mask: int):
    part = (mask - 1) & mask
    while part:
        yield part
        part = (part - 1) & mask


def pascal(n: int, r: int) -> int:
    row = [1]
    for _ in range(n):
        row = [1, *(row[index] + row[index + 1] for index in range(len(row) - 1)), 1]
    return row[r] if r < len(row) else 0


class Replay:
    def __init__(self, maximum_n: int, strong_size: int):
        self.maximum_n = maximum_n
        self.strong_size = strong_size
        self.triples = triples(maximum_n)
        self.positions = {triple: index for index, triple in enumerate(self.triples)}
        self.analysis_cache: dict[
            tuple[int, int], None | dict[tuple[int, int, int], int]
        ] = {}

    def crossing(self, support: int, lower: int) -> int:
        answer = 0
        for position, (i, j, k) in enumerate(self.triples):
            selected = (1 << i) | (1 << j) | (1 << k)
            if selected & support != selected:
                continue
            count = (selected & lower).bit_count()
            if count in (1, 2) and lower & (1 << j):
                answer |= 1 << position
        return answer

    @functools.cache
    def colorings(self, support: int) -> tuple[int, ...]:
        if support.bit_count() == 1:
            return (0,)
        answer = set()
        for lower in proper_parts(support):
            upper = support ^ lower
            fixed = self.crossing(support, lower)
            for lower_bits in self.colorings(lower):
                for upper_bits in self.colorings(upper):
                    answer.add(lower_bits | upper_bits | fixed)
        return tuple(sorted(answer))

    def color(self, bits: int, i: int, j: int, k: int) -> bool:
        return bool(bits & (1 << self.positions[i, j, k]))

    def contains_strong(self, bits: int, support: int) -> bool:
        if support.bit_count() < self.strong_size:
            return False
        vertices = tuple(
            vertex
            for vertex in range(self.maximum_n)
            if support & (1 << vertex)
        )
        for chosen in itertools.combinations(vertices, self.strong_size):
            valid = True
            for a, b, c, d in itertools.combinations(chosen, 4):
                if self.color(bits, a, b, c) != self.color(bits, a, b, d):
                    valid = False
                    break
                if self.color(bits, a, c, d) != self.color(bits, b, c, d):
                    valid = False
                    break
            if valid:
                return True
        return False

    def ranks(
        self, bits: int, support: int
    ) -> None | dict[tuple[int, int, int], int]:
        key = support, bits
        if key in self.analysis_cache:
            return self.analysis_cache[key]
        if self.contains_strong(bits, support):
            self.analysis_cache[key] = None
            return None
        vertices = tuple(
            vertex
            for vertex in range(self.maximum_n)
            if support & (1 << vertex)
        )
        answer = {}
        for left, right in itertools.combinations(vertices, 2):
            middle_vertices = tuple(
                vertex for vertex in vertices if left < vertex < right
            )
            for color in (0, 1):
                best = 2
                for middle_mask in range(1 << len(middle_vertices)):
                    middle = tuple(
                        vertex
                        for index, vertex in enumerate(middle_vertices)
                        if middle_mask & (1 << index)
                    )
                    chain = (left, *middle, right)
                    size = len(chain)
                    if size <= best or size >= self.strong_size:
                        continue
                    if all(
                        self.color(bits, *triple) == bool(color)
                        for triple in itertools.combinations(chain, 3)
                    ):
                        best = size
                answer[color, left, right] = best
        self.analysis_cache[key] = answer
        return answer


def interval_frontier(pairs: list[tuple[int, int]]) -> tuple[tuple[int, int], ...]:
    """Find inclusion-minimal intervals by a separate skyline algorithm."""
    minimum_right: int | None = None
    answer = []
    for left, right in sorted(pairs, key=lambda pair: (-pair[0], pair[1])):
        if minimum_right is None or right < minimum_right:
            answer.append((left, right))
            minimum_right = right
    return tuple(sorted(answer))


def groups(
    local: dict[tuple[int, int, int], int],
    support: int,
    lower: int,
    maximum_n: int,
) -> tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...]:
    vertices = tuple(
        vertex for vertex in range(maximum_n) if support & (1 << vertex)
    )
    collected: defaultdict[tuple[int, int], list[tuple[int, int]]] = defaultdict(list)
    for left, right in itertools.combinations(vertices, 2):
        if bool(lower & (1 << left)) == bool(lower & (1 << right)):
            continue
        for color in (0, 1):
            rank = local[color, left, right]
            if rank >= 3:
                collected[color, rank].append((left, right))
    return tuple(
        (color, rank, interval_frontier(pairs))
        for (color, rank), pairs in sorted(collected.items())
    )


def projected_endpoint_has_chain(
    machine: Replay,
    bits: int,
    vertices: tuple[int, ...],
    color: int,
    size: int,
) -> bool:
    """Direct subset replay for a projected endpoint cup or cap."""
    for selected in itertools.combinations(vertices, size):
        uniform = True
        for triple in itertools.combinations(selected, 3):
            if machine.color(bits, *triple) != bool(color):
                uniform = False
                break
        if uniform:
            return True
    return False


def endpoint_projection_passes(
    machine: Replay,
    bits: int,
    vertices: tuple[int, ...],
    color: int,
    rank: int,
) -> bool:
    """Replay the two avoidances needed by the direct cup--cap shortcut."""
    target = projected_endpoint_has_chain(
        machine, bits, vertices, color, rank + 1
    )
    opposite = projected_endpoint_has_chain(
        machine,
        bits,
        vertices,
        1 - color,
        machine.strong_size + 1 - rank,
    )
    return not target and not opposite


def endpoint_rank_heights(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    endpoint: int,
    color: int,
    rank: int,
    strong_size: int,
    incoming: bool,
) -> tuple[int, ...]:
    """Reconstruct an ideal by its nonincreasing row lengths."""
    columns = strong_size - rank - 1
    heights = []
    for row in range(rank - 1):
        same_threshold = row + 2
        height = 0
        for vertex in vertices:
            if incoming:
                if vertex >= endpoint:
                    continue
                same_rank = local[color, vertex, endpoint]
                opposite_rank = local[1 - color, vertex, endpoint]
            else:
                if vertex <= endpoint:
                    continue
                same_rank = local[color, endpoint, vertex]
                opposite_rank = local[1 - color, endpoint, vertex]
            if same_rank >= same_threshold:
                height = max(height, min(columns, max(0, opposite_rank - 1)))
        heights.append(height)
    if any(heights[index] < heights[index + 1]
           for index in range(len(heights) - 1)):
        raise AssertionError("rank heights are not a lower ideal")
    return tuple(heights)


def height_ideals(rows: int, columns: int) -> tuple[tuple[int, ...], ...]:
    """Enumerate ideals as weakly decreasing bounded height words."""
    return tuple(
        heights
        for heights in itertools.product(range(columns + 1), repeat=rows)
        if all(
            heights[index] >= heights[index + 1]
            for index in range(rows - 1)
        )
    )


def height_interval(
    ideals: tuple[tuple[int, ...], ...],
    first: tuple[int, ...],
    second: tuple[int, ...],
) -> tuple[tuple[int, ...], ...]:
    lower = tuple(min(a, b) for a, b in zip(first, second, strict=True))
    upper = tuple(max(a, b) for a, b in zip(first, second, strict=True))
    return tuple(
        ideal
        for ideal in ideals
        if all(a <= value <= b
               for a, value, b in zip(lower, ideal, upper, strict=True))
    )


def height_mask_hex(ideal: tuple[int, ...], columns: int) -> str:
    mask = 0
    for row, height in enumerate(ideal):
        for column in range(height):
            mask |= 1 << (row * columns + column)
    return f"{mask:x}"


def replay_distinct_representatives(
    candidates: tuple[tuple[tuple[int, ...], ...], ...]
) -> bool:
    """Backtrack on the smallest remaining candidate family."""
    remaining = set(range(len(candidates)))

    def search(used: set[tuple[int, ...]]) -> bool:
        if not remaining:
            return True
        span = min(
            remaining,
            key=lambda index: sum(
                ideal not in used for ideal in candidates[index]
            ),
        )
        choices = [ideal for ideal in candidates[span] if ideal not in used]
        if not choices:
            return False
        remaining.remove(span)
        try:
            return any(search(used | {ideal}) for ideal in choices)
        finally:
            remaining.add(span)

    return search(set())


def replay_transition_candidates(
    local: dict[tuple[int, int, int], int],
    vertices: tuple[int, ...],
    frontier: tuple[tuple[int, int], ...],
    color: int,
    rank: int,
    strong_size: int,
) -> tuple[
    tuple[tuple[tuple[int, ...], ...], ...],
    tuple[tuple[tuple[int, ...], ...], ...],
    tuple[tuple[tuple[int, ...], ...], ...],
    tuple[tuple[tuple[int, ...], ...], ...],
]:
    columns = strong_size - rank - 1
    ideals = height_ideals(rank - 1, columns)
    ideal_key = lambda ideal: int(height_mask_hex(ideal, columns), 16)
    two_way = []
    left_only = []
    right_only = []
    fixed_four = []
    for left, right in frontier:
        intervals = []
        fixed = set()
        for endpoint in (left, right):
            past = endpoint_rank_heights(
                local, vertices, endpoint, color, rank, strong_size, True
            )
            future = endpoint_rank_heights(
                local, vertices, endpoint, color, rank, strong_size, False
            )
            intervals.append(
                tuple(sorted(height_interval(ideals, past, future), key=ideal_key))
            )
            fixed.update((past, future))
        left_only.append(intervals[0])
        right_only.append(intervals[1])
        two_way.append(
            tuple(sorted(set(intervals[0]) | set(intervals[1]), key=ideal_key))
        )
        fixed_four.append(tuple(sorted(fixed, key=ideal_key)))
    return tuple(two_way), tuple(left_only), tuple(right_only), tuple(fixed_four)


def update_digest(
    digest,
    support: int,
    lower: int,
    bits: int,
    local_groups: None | tuple[tuple[int, int, tuple[tuple[int, int], ...]], ...],
) -> None:
    if local_groups is None:
        record = ["terminal", support, lower, bits]
    else:
        record = [
            "open",
            support,
            lower,
            bits,
            [
                [color, rank, [[left, right] for left, right in frontier]]
                for color, rank, frontier in local_groups
            ],
        ]
    digest.update(json.dumps(record, separators=(",", ":")).encode())
    digest.update(b"\n")


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


def replay(maximum_n: int, strong_size: int) -> dict[str, object]:
    machine = Replay(maximum_n, strong_size)
    full = (1 << maximum_n) - 1
    machine.colorings(full)
    totals: Counter[str] = Counter()
    by_size: dict[str, Counter[str]] = {}
    rank_rows: dict[tuple[int, int], Counter[str]] = {}
    projection_rows: dict[tuple[int, int], Counter[str]] = {}
    transition_rows: dict[tuple[int, int], Counter[str]] = {}
    projection_examples: dict[tuple[int, int], dict[str, object]] = {}
    transition_failure = None
    fixed_failure_examples: dict[tuple[int, int], dict[str, object]] = {}
    examples: dict[tuple[int, int], dict[str, object]] = {}
    first_violation = None
    digest = hashlib.sha256()

    for size in range(2, maximum_n + 1):
        row: Counter[str] = Counter()
        for support in range(1, full + 1):
            if support.bit_count() != size:
                continue
            vertices = tuple(
                vertex
                for vertex in range(maximum_n)
                if support & (1 << vertex)
            )
            for lower in proper_parts(support):
                upper = support ^ lower
                fixed = machine.crossing(support, lower)
                seen = set()
                for lower_bits in machine.colorings(lower):
                    for upper_bits in machine.colorings(upper):
                        bits = lower_bits | upper_bits | fixed
                        if bits in seen:
                            raise AssertionError("non-unique root context")
                        seen.add(bits)
                        row["root_contexts"] += 1
                        local = machine.ranks(bits, support)
                        if local is None:
                            row["terminal_contexts"] += 1
                            update_digest(digest, support, lower, bits, None)
                            continue
                        row["open_contexts"] += 1
                        local_groups = groups(local, support, lower, maximum_n)
                        update_digest(digest, support, lower, bits, local_groups)
                        for color, rank, frontier in local_groups:
                            row["rank_group_checks"] += 1
                            key = color, rank
                            rank_row = rank_rows.setdefault(key, Counter())
                            capacity = pascal(strong_size - 2, rank - 1)
                            rank_row["group_count"] += 1
                            rank_row["max_frontier"] = max(
                                rank_row["max_frontier"], len(frontier)
                            )
                            if len(frontier) == capacity:
                                rank_row["saturation_count"] += 1
                                examples.setdefault(
                                    key,
                                    make_example(support, lower, bits, frontier),
                                )
                            if len(frontier) > capacity:
                                row["violations"] += 1
                                if first_violation is None:
                                    first_violation = {
                                        **make_example(
                                            support, lower, bits, frontier
                                        ),
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
                            left_ok = endpoint_projection_passes(
                                machine, bits, left_endpoints, color, rank
                            )
                            right_ok = endpoint_projection_passes(
                                machine, bits, right_endpoints, color, rank
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
                                        **make_example(
                                            support, lower, bits, frontier
                                        ),
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
                            ) = replay_transition_candidates(
                                local,
                                vertices,
                                frontier,
                                color,
                                rank,
                                strong_size,
                            )
                            if not replay_distinct_representatives(left_intervals):
                                transition_row["left_only_failures"] += 1
                            if not replay_distinct_representatives(right_intervals):
                                transition_row["right_only_failures"] += 1
                            if not replay_distinct_representatives(fixed_four):
                                transition_row["fixed_four_failures"] += 1
                                fixed_failure_examples.setdefault(
                                    key,
                                    {
                                        **make_example(
                                            support, lower, bits, frontier
                                        ),
                                        "candidate_ideals_hex": [
                                            [
                                                height_mask_hex(
                                                    ideal,
                                                    strong_size - rank - 1,
                                                )
                                                for ideal in candidates
                                            ]
                                            for candidates in fixed_four
                                        ],
                                    },
                                )
                            if not replay_distinct_representatives(two_way):
                                transition_row["two_way_failures"] += 1
                                if transition_failure is None:
                                    transition_failure = {
                                        **make_example(
                                            support, lower, bits, frontier
                                        ),
                                        "color": "cup" if color else "cap",
                                        "rank": rank,
                                        "candidate_ideals_hex": [
                                            [
                                                height_mask_hex(
                                                    ideal,
                                                    strong_size - rank - 1,
                                                )
                                                for ideal in candidates
                                            ]
                                            for candidates in two_way
                                        ],
                                    }
        by_size[str(size)] = row
        totals.update(row)

    rank_census = {}
    for (color, rank), row in sorted(rank_rows.items()):
        capacity = pascal(strong_size - 2, rank - 1)
        rank_census[f"{'cup' if color else 'cap'},{rank}"] = {
            "capacity": capacity,
            "group_count": row["group_count"],
            "max_frontier": row["max_frontier"],
            "minimum_observed_slack": capacity - row["max_frontier"],
            "saturation_count": row["saturation_count"],
        }
    saturation_examples = {
        f"{'cup' if color else 'cap'},{rank}": value
        for (color, rank), value in sorted(examples.items())
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
        "statistics": {
            "totals": dict(sorted(totals.items())),
            "by_support_size": {
                size: dict(sorted(row.items())) for size, row in by_size.items()
            },
            "analyzed_local_states": len(machine.analysis_cache),
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
        "first_saturation_examples": saturation_examples,
        "first_violation": first_violation,
        "canonical_context_sha256": digest.hexdigest(),
    }


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
        parameters = manifest["parameters"]
        actual = replay(
            int(parameters["maximum_n"]), int(parameters["strong_size"])
        )
        checks.update(
            {
                "statistics": actual["statistics"] == manifest["statistics"],
                "rank_census": actual["rank_census"] == manifest["rank_census"],
                "endpoint_projection_falsifier": (
                    actual["endpoint_projection_falsifier"]
                    == manifest["endpoint_projection_falsifier"]
                ),
                "endpoint_transition_hall_gate": (
                    actual["endpoint_transition_hall_gate"]
                    == manifest["endpoint_transition_hall_gate"]
                ),
                "saturation_examples": (
                    actual["first_saturation_examples"]
                    == manifest["first_saturation_examples"]
                ),
                "first_violation": (
                    actual["first_violation"] == manifest["first_violation"]
                ),
                "canonical_digest": (
                    actual["canonical_context_sha256"]
                    == manifest["canonical_context_sha256"]
                ),
            }
        )
    result = {
        "manifest": str(args.manifest),
        "mode": "source-only" if args.source_only else "exhaustive",
        "source_checks": source_checks,
        "checks": checks,
        "ok": all(checks.values()),
    }
    print(json.dumps(result, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
