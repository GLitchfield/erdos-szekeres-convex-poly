#!/usr/bin/env python3
"""Find the targeted k=6, n=9 singleton-root all-gap collision.

This is a bounded redirect experiment.  It enumerates only decomposable
colorings of the fixed eight-vertex upper child, not all nine-leaf colorings.
The emitted compact certificate contains decomposition trees for the first
pair of open parents with equal complete child all-gap profiles and unequal
parent profiles.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import os
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import TypeAlias


Tree: TypeAlias = int | tuple["Tree", "Tree"]
N = 9
K = 6
LOWER = 1 << 1
FULL = (1 << N) - 1
UPPER = FULL ^ LOWER
TRIPLES = tuple(itertools.combinations(range(N), 3))
POSITIONS = {triple: index for index, triple in enumerate(TRIPLES)}


@functools.cache
def supported_triples(mask: int) -> int:
    answer = 0
    for index, triple in enumerate(TRIPLES):
        selected = sum(1 << vertex for vertex in triple)
        if selected & mask == selected:
            answer |= 1 << index
    return answer


@functools.cache
def crossing_bits(mask: int, lower: int) -> int:
    answer = 0
    for index, (i, j, k) in enumerate(TRIPLES):
        selected = (1 << i) | (1 << j) | (1 << k)
        if selected & mask != selected:
            continue
        count = (selected & lower).bit_count()
        if 0 < count < 3 and lower & (1 << j):
            answer |= 1 << index
    return answer


def proper_submasks(mask: int):
    child = (mask - 1) & mask
    while child:
        yield child
        child = (child - 1) & mask


def enumerate_upper_colorings() -> dict[int, Tree]:
    states: dict[int, dict[int, Tree]] = {}
    for size in range(1, UPPER.bit_count() + 1):
        mask = UPPER
        while mask:
            if mask.bit_count() == size:
                if size == 1:
                    states[mask] = {0: (mask & -mask).bit_length() - 1}
                else:
                    answers: dict[int, Tree] = {}
                    for lower in proper_submasks(mask):
                        upper = mask ^ lower
                        fixed = crossing_bits(mask, lower)
                        for left_bits, left_tree in sorted(states[lower].items()):
                            for right_bits, right_tree in sorted(states[upper].items()):
                                bits = left_bits | right_bits | fixed
                                answers.setdefault(bits, (left_tree, right_tree))
                    states[mask] = answers
            mask = (mask - 1) & UPPER
    return states[UPPER]


@dataclass(frozen=True)
class Chain:
    vertices: tuple[int, ...]
    size: int
    minimum: int
    maximum: int
    required: int


def chains(mask: int) -> tuple[Chain, ...]:
    vertices = tuple(i for i in range(N) if mask & (1 << i))
    return tuple(
        Chain(
            vertices=chain,
            size=size,
            minimum=chain[0],
            maximum=chain[-1],
            required=supported_triples(sum(1 << vertex for vertex in chain)),
        )
        for size in range(1, min(K, len(vertices)) + 1)
        for chain in itertools.combinations(vertices, size)
    )


FULL_CHAINS = chains(FULL)
UPPER_CHAINS = chains(UPPER)


def is_strong(bits: int, chain: tuple[int, ...]) -> bool:
    for a, b, c, d in itertools.combinations(chain, 4):
        if bool(bits & (1 << POSITIONS[(a, b, c)])) != bool(
                bits & (1 << POSITIONS[(a, b, d)])):
            return False
        if bool(bits & (1 << POSITIONS[(a, c, d)])) != bool(
                bits & (1 << POSITIONS[(b, c, d)])):
            return False
    return True


def profile(bits: int, chain_data: tuple[Chain, ...], strong_flag: bool) -> tuple[tuple[int, ...], ...]:
    values = [[0] * 6 for _ in range(N + 1)]
    has_strong = False
    for chain in chain_data:
        cup = bits & chain.required == chain.required
        cap = bits & chain.required == 0
        if strong_flag and chain.size == K and not has_strong:
            has_strong = is_strong(bits, chain.vertices)
        if not cup and not cap:
            continue
        for gap in range(N + 1):
            relation = 0 if gap <= chain.minimum else 1 if gap > chain.maximum else 2
            if cup:
                values[gap][relation] = max(values[gap][relation], chain.size)
            if cap:
                values[gap][3 + relation] = max(values[gap][3 + relation], chain.size)
    return tuple(tuple(row) + (int(has_strong),) for row in values)


def tree_json(tree: Tree) -> object:
    if isinstance(tree, int):
        return tree
    return {"lower": tree_json(tree[0]), "upper": tree_json(tree[1])}


def git_revision(repo: Path) -> str:
    completed = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo, check=True, text=True, stdout=subprocess.PIPE,
    )
    return completed.stdout.strip()


def first_difference(left, right) -> dict[str, object]:
    for gap, (a, b) in enumerate(zip(left, right)):
        if a != b:
            fields = (
                "cup_anchor_left", "cup_anchor_right", "cup_straddled",
                "cap_anchor_left", "cap_anchor_right", "cap_straddled",
                "contains_strong_six",
            )
            positions = [index for index, values in enumerate(zip(a, b)) if values[0] != values[1]]
            return {
                "gap": gap,
                "fields": [fields[index] for index in positions],
                "left": list(a),
                "right": list(b),
            }
    raise AssertionError("the collision outputs were equal")


def search() -> dict[str, object]:
    upper_colorings = enumerate_upper_colorings()
    width = (len(TRIPLES) + 3) // 4
    digest = hashlib.sha256(
        "".join(f"{bits:0{width}x}\n" for bits in sorted(upper_colorings)).encode()
    ).hexdigest()
    fixed = crossing_bits(FULL, LOWER)
    seen: dict[tuple[tuple[int, ...], ...], tuple[tuple[tuple[int, ...], ...], int, int, Tree]] = {}
    open_count = 0
    collision_count = 0
    first = None
    for upper_bits, upper_tree in sorted(upper_colorings.items()):
        parent_bits = upper_bits | fixed
        parent_profile = profile(parent_bits, FULL_CHAINS, True)
        if parent_profile[0][-1]:
            # The strong-set flag is independent of the gap.
            continue
        open_count += 1
        child_profile = profile(upper_bits, UPPER_CHAINS, False)
        previous = seen.get(child_profile)
        record = parent_profile, upper_bits, parent_bits, upper_tree
        if previous is None:
            seen[child_profile] = record
        elif previous[0] != parent_profile:
            collision_count += 1
            if first is None:
                first = previous, record, child_profile
    if first is None:
        raise RuntimeError("no targeted collision found")
    left, right, child_profile = first
    repo = Path(__file__).resolve().parent.parent

    def witness(record) -> dict[str, object]:
        parent_profile, upper_bits, parent_bits, upper_tree = record
        return {
            "upper_coloring_hex": f"{upper_bits:0{width}x}",
            "parent_coloring_hex": f"{parent_bits:0{width}x}",
            "upper_tree": tree_json(upper_tree),
            "parent_profile": [list(row) for row in parent_profile],
        }

    return {
        "schema_version": 1,
        "producer": "scripts/find_decomposable_context_collision.py",
        "revision": git_revision(repo),
        "n": N,
        "k": K,
        "lower_mask_hex": f"{LOWER:x}",
        "upper_mask_hex": f"{UPPER:x}",
        "crossing_bits_hex": f"{fixed:0{width}x}",
        "profile_fields": [
            "cup_anchor_left", "cup_anchor_right", "cup_straddled",
            "cap_anchor_left", "cap_anchor_right", "cap_straddled",
            "contains_strong_six",
        ],
        "search_summary": {
            "upper_coloring_count": len(upper_colorings),
            "upper_colorings_sha256": digest,
            "open_parent_count": open_count,
            "distinct_open_input_count": len(seen),
            "collision_observation_count": collision_count,
        },
        "equal_upper_all_gap_profile": [list(row) for row in child_profile],
        "first_difference": first_difference(left[0], right[0]),
        "left": witness(left),
        "right": witness(right),
    }


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    write_atomic(args.output, search())
    print(args.output)


if __name__ == "__main__":
    main()
