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
    examples: dict[tuple[int, int], dict[str, object]] = {}
    first_violation = None
    digest = hashlib.sha256()

    for size in range(2, maximum_n + 1):
        row: Counter[str] = Counter()
        for support in range(1, full + 1):
            if support.bit_count() != size:
                continue
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
    return {
        "statistics": {
            "totals": dict(sorted(totals.items())),
            "by_support_size": {
                size: dict(sorted(row.items())) for size, row in by_size.items()
            },
            "analyzed_local_states": len(machine.analysis_cache),
        },
        "rank_census": rank_census,
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
