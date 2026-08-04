#!/usr/bin/env python3
"""Independently replay the incoming-star prefix-control census.

This checker imports no producer module.  It regenerates recursively
deep-below colorings with a local subset recurrence and computes pair turn
languages directly from increasing chains, rather than using the producer's
predecessor dynamic program.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
from collections import Counter
from functools import lru_cache
from pathlib import Path


def source_digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(value) -> object:
    if isinstance(value, tuple):
        return [canonical(item) for item in value]
    return value


def update_digest(digest, value) -> None:
    digest.update(
        (json.dumps(canonical(value), separators=(",", ":")) + "\n").encode()
    )


class IndependentReplay:
    def __init__(self, maximum_n: int, depth: int, strong_size: int):
        self.maximum_n = maximum_n
        self.depth = depth
        self.strong_size = strong_size
        self.triples = tuple(itertools.combinations(range(maximum_n), 3))
        self.positions = {triple: i for i, triple in enumerate(self.triples)}
        self.triple_masks = {}
        self.states = {}
        full = (1 << maximum_n) - 1
        for mask in range(1, full + 1):
            bits = 0
            for i, triple in enumerate(self.triples):
                selected = sum(1 << vertex for vertex in triple)
                if selected & mask == selected:
                    bits |= 1 << i
            self.triple_masks[mask] = bits

    def vertices(self, mask: int) -> tuple[int, ...]:
        return tuple(
            vertex
            for vertex in range(self.maximum_n)
            if mask & (1 << vertex)
        )

    def turn(self, bits: int, a: int, b: int, c: int) -> int:
        return int(bool(bits & (1 << self.positions[(a, b, c)])))

    def crossing_bits(self, mask: int, lower: int) -> int:
        answer = 0
        for i, (a, b, c) in enumerate(self.triples):
            selected = (1 << a) | (1 << b) | (1 << c)
            if selected & mask != selected:
                continue
            in_lower = (selected & lower).bit_count()
            if 0 < in_lower < 3 and lower & (1 << b):
                answer |= 1 << i
        return answer

    def enumerate_states(self) -> None:
        full = (1 << self.maximum_n) - 1
        for size in range(1, self.maximum_n + 1):
            for mask in range(1, full + 1):
                if mask.bit_count() != size:
                    continue
                if size == 1:
                    self.states[mask] = frozenset((0,))
                    continue
                colorings = set()
                for lower in range(1, mask):
                    if lower & mask != lower or lower == mask:
                        continue
                    upper = mask ^ lower
                    fixed = self.crossing_bits(mask, lower)
                    colorings.update(
                        lower_bits | upper_bits | fixed
                        for lower_bits in self.states[lower]
                        for upper_bits in self.states[upper]
                    )
                self.states[mask] = frozenset(colorings)

    @lru_cache(None)
    def pair_languages(self, mask: int, bits: int) -> tuple[tuple[int, int, int], ...]:
        vertices = self.vertices(mask)
        records = []
        for v_index, v in enumerate(vertices):
            for u in vertices[:v_index]:
                predecessors = tuple(w for w in vertices if w < u)
                language = 0
                for length in range(min(self.depth, len(predecessors)) + 1):
                    for prefix in itertools.combinations(predecessors, length):
                        chain = prefix + (u, v)
                        word = 0
                        for a, b, c in zip(chain, chain[1:], chain[2:]):
                            word = (word << 1) | self.turn(bits, a, b, c)
                        code = (1 << length) - 1 + word
                        language |= 1 << code
                records.append((u, v, language))
        return tuple(records)

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
        return (
            tuple(
                self.prefix_spectrum(lower, lower_bits, cut)
                for cut in self.vertices(upper)
            ),
            tuple(
                self.prefix_spectrum(upper, upper_bits, cut)
                for cut in self.vertices(lower)
            ),
        )

    @lru_cache(None)
    def is_open(self, mask: int, bits: int) -> bool:
        vertices = self.vertices(mask)
        for chosen in itertools.combinations(vertices, self.strong_size):
            if all(
                self.turn(bits, a, b, c) == self.turn(bits, a, b, d)
                and self.turn(bits, a, c, d) == self.turn(bits, b, c, d)
                for a, b, c, d in itertools.combinations(chosen, 4)
            ):
                return False
        return True

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

    def recovery_layer(self, n: int, mask: int) -> dict[str, object]:
        seen = {}
        collisions = 0
        first_collision = None
        digest = hashlib.sha256()
        for bits in sorted(self.states[mask]):
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
            "coloring_count": len(self.states[mask]),
            "incoming_star_spectrum_count": len(seen),
            "ordered_star_collision_count": collisions,
            "first_ordered_star_collision": first_collision,
            "sha256": digest.hexdigest(),
        }

    def root_layer(self, n: int, mask: int) -> tuple[dict[str, object], object]:
        seen = {}
        fibers: Counter = Counter()
        digest = hashlib.sha256()
        counts = Counter()
        first = {"prefix": None, "ordered": None, "parent": None}
        positive = None
        child_alphabet = set()
        parent_alphabet = set()

        for lower in range(1, mask):
            upper = mask ^ lower
            fixed = self.crossing_bits(mask, lower)
            for lower_bits in sorted(self.states[lower]):
                lower_state = self.spectrum(lower, lower_bits)
                lower_ordered = self.ordered_stars(lower, lower_bits)
                child_alphabet.add(lower_state)
                for upper_bits in sorted(self.states[upper]):
                    parent = lower_bits | upper_bits | fixed
                    if not self.is_open(mask, parent):
                        continue
                    counts["observations"] += 1
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
                        digest,
                        (n, lower, parent, lower_bits, upper_bits, key, query, output),
                    )
                    previous = seen.get(key)
                    record = (query, ordered, output, parent, lower_bits, upper_bits)
                    if previous is None:
                        seen[key] = record
                        continue
                    for name, index in (("prefix", 0), ("ordered", 1), ("parent", 2)):
                        if previous[index] != record[index]:
                            counts[name] += 1
                            if first[name] is None:
                                first[name] = self.collision_record(lower, previous, record)
                    if positive is None and previous[3] != parent:
                        positive = self.collision_record(lower, previous, record)

        observations = counts["observations"]
        return {
            "open_root_observation_count": observations,
            "distinct_fixed_root_input_count": len(seen),
            "repeated_input_observation_count": observations - len(seen),
            "maximum_input_fiber_size": max(fibers.values(), default=0),
            "child_spectrum_alphabet_size": len(child_alphabet),
            "parent_spectrum_alphabet_size": len(parent_alphabet),
            "prefix_query_collision_count": counts["prefix"],
            "ordered_child_star_collision_count": counts["ordered"],
            "parent_spectrum_collision_count": counts["parent"],
            "first_prefix_query_collision": first["prefix"],
            "first_ordered_child_star_collision": first["ordered"],
            "first_parent_spectrum_collision": first["parent"],
            "observation_sha256": digest.hexdigest(),
        }, positive

    def replay(self) -> dict[str, object]:
        self.enumerate_states()
        layers = {}
        totals = Counter()
        positive = None
        for n in range(1, self.maximum_n + 1):
            mask = (1 << n) - 1
            recovery = self.recovery_layer(n, mask)
            root = None
            if n >= 2:
                root, witness = self.root_layer(n, mask)
                if positive is None and witness is not None:
                    positive = {"n": n, **witness}
                for field in (
                    "open_root_observation_count",
                    "distinct_fixed_root_input_count",
                    "prefix_query_collision_count",
                    "ordered_child_star_collision_count",
                    "parent_spectrum_collision_count",
                ):
                    totals[field] += root[field]
            layers[str(n)] = {"global_recovery": recovery, "root_transition": root}
        return {
            "layers": layers,
            "totals": dict(sorted(totals.items())),
            "positive_regression": positive,
        }

    def tree_vertices(self, tree) -> frozenset[int]:
        if isinstance(tree, int):
            return frozenset((tree,))
        return self.tree_vertices(tree["lower"]) | self.tree_vertices(tree["upper"])

    def tree_turn(self, tree, a: int, b: int, c: int) -> int:
        if isinstance(tree, int):
            raise AssertionError("three leaves cannot descend to a leaf")
        lower = self.tree_vertices(tree["lower"])
        membership = (a in lower, b in lower, c in lower)
        if all(membership):
            return self.tree_turn(tree["lower"], a, b, c)
        if not any(membership):
            return self.tree_turn(tree["upper"], a, b, c)
        return int(membership[1])

    def tree_coloring(self, tree, n: int) -> int:
        answer = 0
        for triple in itertools.combinations(range(n), 3):
            if self.tree_turn(tree, *triple):
                answer |= 1 << self.positions[triple]
        return answer


def strip_trees(witness):
    if witness is None:
        return None
    answer = copy.deepcopy(witness)
    for label in ("first", "second"):
        answer[label].pop("parent_tree", None)
    return answer


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported schema version")

    repo = Path(__file__).resolve().parent.parent
    for source in manifest["sources"].values():
        path = repo / source["path"]
        if source_digest(path) != source["sha256"]:
            raise SystemExit(f"source digest mismatch: {source['path']}")

    parameters = manifest["parameters"]
    replay = IndependentReplay(
        parameters["maximum_n"],
        parameters["turn_word_depth"],
        parameters["strong_size"],
    )
    computed = replay.replay()
    checks = {
        "layers": computed["layers"] == manifest["layers"],
        "totals": computed["totals"] == manifest["totals"],
        "positive_regression": computed["positive_regression"]
        == strip_trees(manifest["positive_regression"]),
    }

    witness = manifest["positive_regression"]
    n = witness["n"]
    for label in ("first", "second"):
        tree = witness[label]["parent_tree"]
        expected = int(witness[label]["parent_coloring_hex"], 16)
        checks[f"{label}_tree_vertices"] = replay.tree_vertices(tree) == frozenset(
            range(n)
        )
        checks[f"{label}_tree_coloring"] = replay.tree_coloring(tree, n) == expected

    if not all(checks.values()):
        failures = ", ".join(name for name, passed in checks.items() if not passed)
        raise SystemExit(f"incoming-star prefix replay failed: {failures}")
    print(json.dumps({"checks": checks, "totals": computed["totals"]}, sort_keys=True))


if __name__ == "__main__":
    main()
