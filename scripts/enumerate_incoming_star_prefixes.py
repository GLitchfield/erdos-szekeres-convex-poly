#!/usr/bin/env python3
"""Produce the bounded incoming-star prefix-control census.

For every recursively decomposable coloring on at most eight ordered leaves
and every compatible root, this producer groups strong-six-open parents by the
fixed root mask and the two child incoming-star spectra.  It checks separately
whether that input determines the root-relevant child prefix queries, the
ordered child star sequences, and the parent incoming-star spectrum.

Pair languages use the predecessor recurrence proved correct in
``ErdosSzekeres/TurnLanguage.lean``.  The independent checker intentionally
recomputes them from increasing chains and does not import this module.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import subprocess
from collections import Counter
from functools import lru_cache
from pathlib import Path

from enumerate_decomposable_contexts import Census, nonempty_submasks


def source_digest(path: Path) -> str:
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


def canonical(value) -> object:
    if isinstance(value, tuple):
        return [canonical(item) for item in value]
    return value


def update_digest(digest, value) -> None:
    digest.update(
        (json.dumps(canonical(value), separators=(",", ":")) + "\n").encode()
    )


class IncomingStarCensus:
    def __init__(self, maximum_n: int, depth: int, strong_size: int):
        self.maximum_n = maximum_n
        self.depth = depth
        self.strong_size = strong_size
        self.census = Census(maximum_n)

    def vertices(self, mask: int) -> tuple[int, ...]:
        return tuple(
            vertex
            for vertex in range(self.maximum_n)
            if mask & (1 << vertex)
        )

    def turn(self, bits: int, a: int, b: int, c: int) -> int:
        position = self.census.positions[(a, b, c)]
        return int(bool(bits & (1 << position)))

    @lru_cache(None)
    def pair_languages(self, mask: int, bits: int) -> tuple[tuple[int, int, int], ...]:
        vertices = self.vertices(mask)
        languages: dict[tuple[int, int], int] = {}
        for v_index, v in enumerate(vertices):
            for u in vertices[:v_index]:
                language = 1
                for w in vertices:
                    if w >= u:
                        break
                    previous = languages[(w, u)]
                    for code in range((1 << self.depth) - 1):
                        if not previous & (1 << code):
                            continue
                        length = (code + 1).bit_length() - 1
                        word = code - ((1 << length) - 1)
                        extension = (word << 1) | self.turn(bits, w, u, v)
                        next_code = (1 << (length + 1)) - 1 + extension
                        language |= 1 << next_code
                languages[(u, v)] = language
        return tuple((u, v, language) for (u, v), language in languages.items())

    @lru_cache(None)
    def ordered_stars(self, mask: int, bits: int) -> tuple[tuple[int, ...], ...]:
        vertices = self.vertices(mask)
        languages = {
            (u, v): language for u, v, language in self.pair_languages(mask, bits)
        }
        return tuple(
            tuple(sorted({languages[(u, v)] for u in vertices if u < v}))
            for v in vertices
        )

    def spectrum(self, mask: int, bits: int) -> tuple[tuple[int, ...], ...]:
        return tuple(sorted(set(self.ordered_stars(mask, bits))))

    def prefix_spectrum(
        self, mask: int, bits: int, cut: int
    ) -> tuple[tuple[int, ...], ...]:
        vertices = self.vertices(mask)
        stars = self.ordered_stars(mask, bits)
        return tuple(
            sorted({star for vertex, star in zip(vertices, stars) if vertex < cut})
        )

    def root_query(
        self, lower: int, lower_bits: int, upper: int, upper_bits: int
    ) -> tuple[tuple[tuple[int, ...], ...], ...]:
        lower_queries = tuple(
            self.prefix_spectrum(lower, lower_bits, cut)
            for cut in self.vertices(upper)
        )
        upper_queries = tuple(
            self.prefix_spectrum(upper, upper_bits, cut)
            for cut in self.vertices(lower)
        )
        return lower_queries, upper_queries

    @lru_cache(None)
    def is_open(self, mask: int, bits: int) -> bool:
        vertices = self.vertices(mask)
        for chosen in itertools.combinations(vertices, self.strong_size):
            strong = True
            for a, b, c, d in itertools.combinations(chosen, 4):
                if self.turn(bits, a, b, c) != self.turn(bits, a, b, d):
                    strong = False
                    break
                if self.turn(bits, a, c, d) != self.turn(bits, b, c, d):
                    strong = False
                    break
            if strong:
                return False
        return True

    @lru_cache(None)
    def decomposition_tree(self, mask: int, bits: int):
        bits &= self.census.triple_masks[mask]
        if mask.bit_count() == 1:
            return self.vertices(mask)[0]
        for lower in sorted(nonempty_submasks(mask)):
            if lower == mask:
                continue
            upper = mask ^ lower
            fixed = self.census.crossing_bits(mask, lower)
            child_bits = bits & (
                self.census.triple_masks[lower]
                | self.census.triple_masks[upper]
            )
            if bits != child_bits | fixed:
                continue
            left = self.decomposition_tree(lower, bits)
            right = self.decomposition_tree(upper, bits)
            if left is not None and right is not None:
                return {"lower": left, "upper": right}
        return None

    def recovery_layer(self, n: int, mask: int) -> dict[str, object]:
        seen: dict[tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]] = {}
        collisions = 0
        first_collision = None
        digest = hashlib.sha256()
        for bits in sorted(self.census.states[mask]):
            state = self.spectrum(mask, bits)
            ordered = self.ordered_stars(mask, bits)
            update_digest(digest, (n, bits, state, ordered))
            previous = seen.get(state)
            if previous is None:
                seen[state] = ordered
            elif previous != ordered:
                collisions += 1
                if first_collision is None:
                    first_collision = {"coloring_hex": f"{bits:x}"}
        return {
            "coloring_count": len(self.census.states[mask]),
            "incoming_star_spectrum_count": len(seen),
            "ordered_star_collision_count": collisions,
            "first_ordered_star_collision": first_collision,
            "sha256": digest.hexdigest(),
        }

    def root_layer(self, n: int, mask: int) -> tuple[dict[str, object], object]:
        seen = {}
        fibers: Counter = Counter()
        observation_digest = hashlib.sha256()
        prefix_collisions = 0
        ordered_collisions = 0
        parent_collisions = 0
        first_prefix_collision = None
        first_ordered_collision = None
        first_parent_collision = None
        positive_regression = None
        observations = 0
        child_alphabet = set()
        parent_alphabet = set()

        for lower in range(1, mask):
            upper = mask ^ lower
            fixed = self.census.crossing_bits(mask, lower)
            for lower_bits in sorted(self.census.states[lower]):
                lower_state = self.spectrum(lower, lower_bits)
                lower_ordered = self.ordered_stars(lower, lower_bits)
                child_alphabet.add(lower_state)
                for upper_bits in sorted(self.census.states[upper]):
                    parent = lower_bits | upper_bits | fixed
                    if not self.is_open(mask, parent):
                        continue
                    observations += 1
                    upper_state = self.spectrum(upper, upper_bits)
                    upper_ordered = self.ordered_stars(upper, upper_bits)
                    child_alphabet.add(upper_state)
                    key = lower, lower_state, upper_state
                    query = self.root_query(lower, lower_bits, upper, upper_bits)
                    ordered = lower_ordered, upper_ordered
                    output = self.spectrum(mask, parent)
                    parent_alphabet.add(output)
                    fibers[key] += 1
                    update_digest(
                        observation_digest,
                        (n, lower, parent, lower_bits, upper_bits, key, query, output),
                    )
                    previous = seen.get(key)
                    record = (query, ordered, output, parent, lower_bits, upper_bits)
                    if previous is None:
                        seen[key] = record
                        continue
                    if previous[0] != query:
                        prefix_collisions += 1
                        if first_prefix_collision is None:
                            first_prefix_collision = self.collision_record(
                                lower, previous, record
                            )
                    if previous[1] != ordered:
                        ordered_collisions += 1
                        if first_ordered_collision is None:
                            first_ordered_collision = self.collision_record(
                                lower, previous, record
                            )
                    if previous[2] != output:
                        parent_collisions += 1
                        if first_parent_collision is None:
                            first_parent_collision = self.collision_record(
                                lower, previous, record
                            )
                    if positive_regression is None and previous[3] != parent:
                        positive_regression = self.collision_record(
                            lower, previous, record
                        )

        layer = {
            "open_root_observation_count": observations,
            "distinct_fixed_root_input_count": len(seen),
            "repeated_input_observation_count": observations - len(seen),
            "maximum_input_fiber_size": max(fibers.values(), default=0),
            "child_spectrum_alphabet_size": len(child_alphabet),
            "parent_spectrum_alphabet_size": len(parent_alphabet),
            "prefix_query_collision_count": prefix_collisions,
            "ordered_child_star_collision_count": ordered_collisions,
            "parent_spectrum_collision_count": parent_collisions,
            "first_prefix_query_collision": first_prefix_collision,
            "first_ordered_child_star_collision": first_ordered_collision,
            "first_parent_spectrum_collision": first_parent_collision,
            "observation_sha256": observation_digest.hexdigest(),
        }
        return layer, positive_regression

    def collision_record(self, lower: int, first, second) -> dict[str, object]:
        def side(record) -> dict[str, object]:
            return {
                "parent_coloring_hex": f"{record[3]:x}",
                "lower_coloring_hex": f"{record[4]:x}",
                "upper_coloring_hex": f"{record[5]:x}",
            }

        return {
            "lower_mask_hex": f"{lower:x}",
            "first": side(first),
            "second": side(second),
        }

    def produce(self) -> dict[str, object]:
        self.census.enumerate_states()
        layers = {}
        positive_regression = None
        totals = Counter()
        for n in range(1, self.maximum_n + 1):
            mask = (1 << n) - 1
            recovery = self.recovery_layer(n, mask)
            root = None
            if n >= 2:
                root, witness = self.root_layer(n, mask)
                if positive_regression is None and witness is not None:
                    positive_regression = {"n": n, **witness}
                totals["open_root_observation_count"] += root[
                    "open_root_observation_count"
                ]
                totals["distinct_fixed_root_input_count"] += root[
                    "distinct_fixed_root_input_count"
                ]
                totals["prefix_query_collision_count"] += root[
                    "prefix_query_collision_count"
                ]
                totals["ordered_child_star_collision_count"] += root[
                    "ordered_child_star_collision_count"
                ]
                totals["parent_spectrum_collision_count"] += root[
                    "parent_spectrum_collision_count"
                ]
            layers[str(n)] = {"global_recovery": recovery, "root_transition": root}

        if positive_regression is not None:
            lower = int(positive_regression["lower_mask_hex"], 16)
            for label in ("first", "second"):
                bits = int(positive_regression[label]["parent_coloring_hex"], 16)
                mask = (1 << positive_regression["n"]) - 1
                positive_regression[label]["parent_tree"] = self.decomposition_tree(
                    mask, bits
                )

        return {
            "schema_version": 1,
            "experiment": "incoming-star-prefix-control",
            "parameters": {
                "maximum_n": self.maximum_n,
                "strong_size": self.strong_size,
                "turn_word_depth": self.depth,
                "turn_encoding": "0=right, 1=left; heap-indexed words; bitset languages",
                "triple_order": (
                    f"lexicographic combinations(range({self.maximum_n}), 3); "
                    "LSB first; 1=left"
                ),
            },
            "layers": layers,
            "totals": dict(sorted(totals.items())),
            "positive_regression": positive_regression,
            "scope": (
                "Exact for recursively deep-below colorings on initial ordered "
                f"sets through n={self.maximum_n}; root transitions are restricted "
                f"to parents avoiding a strong {self.strong_size}-set."
            ),
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-n", type=int, default=8)
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--strong-size", type=int, default=6)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 2 <= args.maximum_n <= 8:
        parser.error("maximum-n must lie between 2 and 8")
    if args.depth < 0 or args.strong_size < 4:
        parser.error("invalid depth or strong size")

    repo = Path(__file__).resolve().parent.parent
    checker = repo / "scripts/check_incoming_star_prefixes.py"
    producer = Path(__file__).resolve()
    result = IncomingStarCensus(
        args.maximum_n, args.depth, args.strong_size
    ).produce()
    result["generation_base_revision"] = git_revision(repo)
    result["sources"] = {
        "producer": {
            "path": str(producer.relative_to(repo)),
            "sha256": source_digest(producer),
        },
        "checker": {
            "path": str(checker.relative_to(repo)),
            "sha256": source_digest(checker),
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    temporary.replace(args.output)
    print(args.output)


if __name__ == "__main__":
    main()
