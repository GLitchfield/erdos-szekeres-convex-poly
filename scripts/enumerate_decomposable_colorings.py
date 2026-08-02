#!/usr/bin/env python3
"""Exactly enumerate colorings induced by recursive deep-below trees.

This is the producer for Wayfinder ticket 0002.  It uses dynamic programming
on labeled leaf subsets and deduplicates by the complete triple-color bit
vector.  Bit ``1`` means ``Turn.left``; triples occur in lexicographic order.
The independent checker intentionally does not import this module.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import subprocess
from collections import Counter
from pathlib import Path
from typing import TypeAlias


Tree: TypeAlias = int | tuple["Tree", "Tree"]


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def subsets(mask: int) -> list[int]:
    result: list[int] = []
    sub = mask
    while sub:
        result.append(sub)
        sub = (sub - 1) & mask
    return result


def enumerate_colorings(n: int) -> tuple[dict[int, Tree], dict[int, int]]:
    """Return witnesses on all leaves and distinct-color counts by subset size."""
    triple_list = triples(n)
    by_subset: dict[int, dict[int, Tree]] = {}
    layer_counts: Counter[int] = Counter()
    full = (1 << n) - 1

    for size in range(1, n + 1):
        for mask in (m for m in range(1, full + 1) if m.bit_count() == size):
            if size == 1:
                leaf = (mask & -mask).bit_length() - 1
                by_subset[mask] = {0: leaf}
                layer_counts[size] += 1
                continue

            colorings: dict[int, Tree] = {}
            for lower in subsets(mask):
                if lower == mask:
                    continue
                upper = mask ^ lower
                crossing = 0
                for position, (i, j, k) in enumerate(triple_list):
                    triple_mask = (1 << i) | (1 << j) | (1 << k)
                    if triple_mask & mask != triple_mask:
                        continue
                    wholly_lower = triple_mask & lower == triple_mask
                    wholly_upper = triple_mask & upper == triple_mask
                    if not wholly_lower and not wholly_upper and lower & (1 << j):
                        crossing |= 1 << position
                for lower_bits, lower_tree in by_subset[lower].items():
                    for upper_bits, upper_tree in by_subset[upper].items():
                        bits = lower_bits | upper_bits | crossing
                        colorings.setdefault(bits, (lower_tree, upper_tree))
            by_subset[mask] = colorings
            layer_counts[size] += len(colorings)

    return by_subset[full], dict(sorted(layer_counts.items()))


def color(bits: int, position: dict[tuple[int, int, int], int],
          i: int, j: int, k: int) -> bool:
    return bool(bits & (1 << position[(i, j, k)]))


def is_strong(bits: int, position: dict[tuple[int, int, int], int],
              vertices: tuple[int, ...]) -> bool:
    for i, j, k, l in itertools.combinations(vertices, 4):
        if color(bits, position, i, j, k) != color(bits, position, i, j, l):
            return False
        if color(bits, position, i, k, l) != color(bits, position, j, k, l):
            return False
    return True


def is_monochromatic(bits: int, position: dict[tuple[int, int, int], int],
                     vertices: tuple[int, ...], expected: bool) -> bool:
    return all(color(bits, position, *t) == expected
               for t in itertools.combinations(vertices, 3))


def is_signotope(bits: int, position: dict[tuple[int, int, int], int], n: int) -> bool:
    for a, b, c, d in itertools.combinations(range(n), 4):
        values = (
            color(bits, position, a, b, c),
            color(bits, position, a, b, d),
            color(bits, position, a, c, d),
            color(bits, position, b, c, d),
        )
        if sum(x != y for x, y in zip(values, values[1:])) > 1:
            return False
    return True


def maximum_size(bits: int, position: dict[tuple[int, int, int], int], n: int,
                 predicate) -> int:
    for size in range(n, 0, -1):
        if any(predicate(bits, position, subset)
               for subset in itertools.combinations(range(n), size)):
            return size
    raise AssertionError("the empty search range cannot occur")


def tree_json(tree: Tree) -> object:
    if isinstance(tree, int):
        return tree
    return {"lower": tree_json(tree[0]), "upper": tree_json(tree[1])}


def git_revision(repo: Path) -> str:
    completed = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo, check=True, text=True, stdout=subprocess.PIPE)
    return completed.stdout.strip()


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 1 <= args.n <= 8:
        parser.error("n must lie between 1 and 8")

    all_colorings, layer_counts = enumerate_colorings(args.n)
    triple_list = triples(args.n)
    position = {triple: i for i, triple in enumerate(triple_list)}
    width = max(1, (len(triple_list) + 3) // 4)
    ordered_bits = sorted(all_colorings)
    digest_input = "".join(f"{bits:0{width}x}\n" for bits in ordered_bits).encode()

    strong_histogram: Counter[int] = Counter()
    cup_histogram: Counter[int] = Counter()
    cap_histogram: Counter[int] = Counter()
    signotope_count = 0
    minimizer_bits: int | None = None
    minimum_strong = args.n + 1
    for bits in ordered_bits:
        strong = maximum_size(bits, position, args.n, is_strong)
        cup = maximum_size(
            bits, position, args.n,
            lambda b, p, s: is_monochromatic(b, p, s, True))
        cap = maximum_size(
            bits, position, args.n,
            lambda b, p, s: is_monochromatic(b, p, s, False))
        strong_histogram[strong] += 1
        cup_histogram[cup] += 1
        cap_histogram[cap] += 1
        if is_signotope(bits, position, args.n):
            signotope_count += 1
        if strong < minimum_strong:
            minimum_strong = strong
            minimizer_bits = bits

    assert minimizer_bits is not None
    repo = Path(__file__).resolve().parent.parent
    manifest = {
        "schema_version": 1,
        "producer": "scripts/enumerate_decomposable_colorings.py",
        "revision": git_revision(repo),
        "n": args.n,
        "triple_order": "lexicographic combinations(range(n), 3); LSB first; 1=left",
        "triple_count": len(triple_list),
        "distinct_coloring_count": len(ordered_bits),
        "distinct_colorings_sha256": hashlib.sha256(digest_input).hexdigest(),
        "dynamic_program_layer_totals": layer_counts,
        "signotope_count": signotope_count,
        "minimum_strong_maximum": minimum_strong,
        "strong_maximum_histogram": dict(sorted(strong_histogram.items())),
        "cup_maximum_histogram": dict(sorted(cup_histogram.items())),
        "cap_maximum_histogram": dict(sorted(cap_histogram.items())),
        "minimum_witness": {
            "coloring_hex": f"{minimizer_bits:0{width}x}",
            "tree": tree_json(all_colorings[minimizer_bits]),
        },
    }
    write_atomic(args.output, manifest)
    print(args.output)


if __name__ == "__main__":
    main()
