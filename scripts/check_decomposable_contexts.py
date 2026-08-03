#!/usr/bin/env python3
"""Independently replay an all-root decomposable context manifest.

This checker imports no producer code.  It reconstructs recursive colorings
with its own subset recurrence, finds compatible roots by testing each parent
color vector against the root law, and recomputes every chain, profile,
restriction, transition collision, and canonical record hash.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


CLIP = 5


def submasks(mask: int):
    candidate = (mask - 1) & mask
    while candidate:
        yield candidate
        candidate = (candidate - 1) & mask


def encode_profile(values: list[int], strong: bool) -> int:
    code = int(strong) << 18
    for position, value in enumerate(values):
        code += value << (3 * position)
    return code


def decode_profile(code: int) -> tuple[int, ...]:
    values = tuple((code >> (3 * position)) & 7 for position in range(6))
    return values + ((code >> 18) & 1,)


def is_subprofile(child: int, parent: int) -> bool:
    a = decode_profile(child)
    b = decode_profile(parent)
    return all(x <= y for x, y in zip(a, b))


@dataclass(frozen=True)
class Facts:
    by_gap: tuple[int, ...]
    four_cups: tuple[int, ...]
    four_caps: tuple[int, ...]
    has_cup_five: bool
    has_cap_five: bool
    has_strong_five: bool
    obeys_signotope: bool


class Replay:
    def __init__(self, maximum_n: int):
        self.maximum_n = maximum_n
        self.triples = tuple(itertools.combinations(range(maximum_n), 3))
        self.index = {triple: position for position, triple in enumerate(self.triples)}
        self.inspection_cache: dict[tuple[int, int], Facts] = {}

    @functools.cache
    def supported_triples(self, mask: int) -> int:
        result = 0
        for position, triple in enumerate(self.triples):
            triple_mask = sum(1 << vertex for vertex in triple)
            if triple_mask & mask == triple_mask:
                result |= 1 << position
        return result

    @functools.cache
    def crossing_assignment(self, parent: int, lower: int) -> int:
        result = 0
        for position, (a, b, c) in enumerate(self.triples):
            chosen = (1 << a) | (1 << b) | (1 << c)
            if chosen & parent != chosen:
                continue
            lower_count = (chosen & lower).bit_count()
            if 0 < lower_count < 3 and lower & (1 << b):
                result |= 1 << position
        return result

    @functools.cache
    def colorings(self, mask: int) -> frozenset[int]:
        if mask.bit_count() == 1:
            return frozenset((0,))
        answers: set[int] = set()
        for lower in submasks(mask):
            upper = mask ^ lower
            crossing = self.crossing_assignment(mask, lower)
            for left in self.colorings(lower):
                for right in self.colorings(upper):
                    answers.add(left | right | crossing)
        return frozenset(answers)

    def valid_root(self, parent_mask: int, bits: int, lower: int) -> tuple[int, int] | None:
        upper = parent_mask ^ lower
        lower_bits = bits & self.supported_triples(lower)
        upper_bits = bits & self.supported_triples(upper)
        if lower_bits not in self.colorings(lower) or upper_bits not in self.colorings(upper):
            return None
        crossing_positions = self.supported_triples(parent_mask) & ~(
            self.supported_triples(lower) | self.supported_triples(upper)
        )
        if bits & crossing_positions != self.crossing_assignment(parent_mask, lower):
            return None
        return lower_bits, upper_bits

    def strong_five(self, bits: int, vertices: tuple[int, ...]) -> bool:
        for a, b, c, d in itertools.combinations(vertices, 4):
            abc = bool(bits & (1 << self.index[(a, b, c)]))
            abd = bool(bits & (1 << self.index[(a, b, d)]))
            acd = bool(bits & (1 << self.index[(a, c, d)]))
            bcd = bool(bits & (1 << self.index[(b, c, d)]))
            if abc != abd or acd != bcd:
                return False
        return True

    def signotope(self, bits: int, vertices: tuple[int, ...]) -> bool:
        for a, b, c, d in itertools.combinations(vertices, 4):
            sequence = (
                bool(bits & (1 << self.index[(a, b, c)])),
                bool(bits & (1 << self.index[(a, b, d)])),
                bool(bits & (1 << self.index[(a, c, d)])),
                bool(bits & (1 << self.index[(b, c, d)])),
            )
            if sum(x != y for x, y in zip(sequence, sequence[1:])) > 1:
                return False
        return True

    def inspect(self, mask: int, bits: int) -> Facts:
        key = mask, bits
        if key in self.inspection_cache:
            return self.inspection_cache[key]
        vertices = tuple(i for i in range(self.maximum_n) if mask & (1 << i))
        maxima = [[0] * 6 for _ in range(self.maximum_n + 1)]
        cups: list[int] = []
        caps: list[int] = []
        cup_five = cap_five = strong_five = False
        for size in range(1, min(CLIP, len(vertices)) + 1):
            for chain in itertools.combinations(vertices, size):
                chain_mask = sum(1 << vertex for vertex in chain)
                required = self.supported_triples(chain_mask)
                cup = bits & required == required
                cap = bits & required == 0
                if size == 4:
                    if cup:
                        cups.append(chain_mask)
                    if cap:
                        caps.append(chain_mask)
                if size == 5:
                    cup_five |= cup
                    cap_five |= cap
                    strong_five |= self.strong_five(bits, chain)
                for gap in range(self.maximum_n + 1):
                    slot = 0 if gap <= chain[0] else 1 if gap > chain[-1] else 2
                    if cup:
                        maxima[gap][slot] = max(maxima[gap][slot], size)
                    if cap:
                        maxima[gap][3 + slot] = max(maxima[gap][3 + slot], size)
        answer = Facts(
            by_gap=tuple(encode_profile(row, strong_five) for row in maxima),
            # Canonical chain records are ordered by their vertex bit mask,
            # independently of this checker's combination traversal.
            four_cups=tuple(sorted(cups)),
            four_caps=tuple(sorted(caps)),
            has_cup_five=cup_five,
            has_cap_five=cap_five,
            has_strong_five=strong_five,
            obeys_signotope=self.signotope(bits, vertices),
        )
        self.inspection_cache[key] = answer
        return answer


def anchor_relation(chain_mask: int, anchor: int) -> str:
    chain = tuple(i for i in range(chain_mask.bit_length()) if chain_mask & (1 << i))
    if anchor < chain[0]:
        return "L"
    if anchor > chain[-1]:
        return "R"
    return "S"


def feed(digest, values) -> None:
    digest.update(("|".join(str(value) for value in values) + "\n").encode())


def witness(previous, output: int, current, n: int, lower: int, gap: int) -> dict[str, object]:
    old_output, old = previous
    return {
        "first": {
            "parent_hex": f"{old[0]:x}",
            "lower_bits_hex": f"{old[1]:x}",
            "upper_bits_hex": f"{old[2]:x}",
            "output_profile": list(decode_profile(old_output)),
        },
        "second": {
            "parent_hex": f"{current[0]:x}",
            "lower_bits_hex": f"{current[1]:x}",
            "upper_bits_hex": f"{current[2]:x}",
            "output_profile": list(decode_profile(output)),
        },
        "n": n,
        "lower_mask_hex": f"{lower:x}",
        "gap": gap,
    }


def note_transition(layer, prefix: str, seen: dict, key, output: int, record,
                    n: int, lower: int, gap: int) -> None:
    old = seen.get(key)
    if old is None:
        seen[key] = output, record
    elif old[0] != output:
        layer[f"{prefix}_collision_count"] += 1
        if layer[f"{prefix}_first_collision"] is None:
            layer[f"{prefix}_first_collision"] = witness(
                old, output, record, n, lower, gap)


def replay(maximum_n: int) -> dict[str, object]:
    check = Replay(maximum_n)
    coloring_hash = hashlib.sha256()
    root_hash = hashlib.sha256()
    anchor_hash = hashlib.sha256()
    alphabet: set[int] = set()
    layers: dict[str, object] = {}

    for n in range(1, maximum_n + 1):
        parent_mask = (1 << n) - 1
        parents = sorted(check.colorings(parent_mask))
        for bits in parents:
            feed(coloring_hash, ("C", n, f"{bits:x}"))
            alphabet.update(check.inspect(parent_mask, bits).by_gap)
        layer = {
            "distinct_coloring_count": len(parents),
            "valid_root_count": 0,
            "singleton_root_count": 0,
            "signotope_count": sum(check.inspect(parent_mask, bits).obeys_signotope for bits in parents),
            "context_record_count": 0,
            "singleton_context_record_count": 0,
            "context_relation_histogram": Counter(),
            "endpoint_transition_checks": 0,
            "endpoint_transition_violations": 0,
            "saturation_checks": 0,
            "saturation_violations": 0,
            "restriction_checks": 0,
            "restriction_violations": 0,
            "local_transition_observations": 0,
            "local_transition_input_count": 0,
            "local_transition_collision_count": 0,
            "local_transition_first_collision": None,
            "local_open_transition_observations": 0,
            "local_open_transition_input_count": 0,
            "local_open_transition_collision_count": 0,
            "local_open_transition_first_collision": None,
            "cross_anchor_transition_observations": 0,
            "cross_anchor_transition_input_count": 0,
            "cross_anchor_transition_collision_count": 0,
            "cross_anchor_transition_first_collision": None,
            "cross_anchor_open_transition_observations": 0,
            "cross_anchor_open_transition_input_count": 0,
            "cross_anchor_open_transition_collision_count": 0,
            "cross_anchor_open_transition_first_collision": None,
            "all_gap_transition_observations": 0,
            "all_gap_transition_input_count": 0,
            "all_gap_transition_collision_count": 0,
            "all_gap_transition_first_collision": None,
            "all_gap_open_transition_observations": 0,
            "all_gap_open_transition_input_count": 0,
            "all_gap_open_transition_collision_count": 0,
            "all_gap_open_transition_first_collision": None,
        }
        if n == 1:
            layers[str(n)] = layer
            continue

        for lower in range(1, parent_mask):
            upper = parent_mask ^ lower
            local: dict = {}
            local_open: dict = {}
            cross: dict = {}
            cross_open: dict = {}
            all_gap: dict = {}
            all_gap_open: dict = {}
            for parent in parents:
                child_bits = check.valid_root(parent_mask, parent, lower)
                if child_bits is None:
                    continue
                lower_bits, upper_bits = child_bits
                layer["valid_root_count"] += 1
                singleton = lower.bit_count() == 1 or upper.bit_count() == 1
                layer["singleton_root_count"] += int(singleton)
                parent_facts = check.inspect(parent_mask, parent)
                lower_facts = check.inspect(lower, lower_bits)
                upper_facts = check.inspect(upper, upper_bits)
                feed(root_hash, (
                    "R", n, f"{parent:x}", f"{lower:x}",
                    int(parent_facts.has_cup_five), int(parent_facts.has_cap_five),
                    int(parent_facts.has_strong_five), int(parent_facts.obeys_signotope),
                ))
                record = parent, lower_bits, upper_bits, lower
                cross_word = tuple(
                    lower_facts.by_gap[q] for q in range(n) if upper & (1 << q)
                ) + tuple(
                    upper_facts.by_gap[q] for q in range(n) if lower & (1 << q)
                )
                for gap in range(n + 1):
                    low = lower_facts.by_gap[gap]
                    high = upper_facts.by_gap[gap]
                    output = parent_facts.by_gap[gap]
                    layer["restriction_checks"] += 2
                    layer["restriction_violations"] += int(not is_subprofile(low, output))
                    layer["restriction_violations"] += int(not is_subprofile(high, output))

                    local_key = gap, low, high
                    note_transition(layer, "local_transition", local, local_key,
                                    output, record, n, lower, gap)
                    layer["local_transition_observations"] += 1
                    if not parent_facts.has_strong_five:
                        layer["local_open_transition_observations"] += 1
                        note_transition(layer, "local_open_transition", local_open,
                                        local_key, output, record, n, lower, gap)

                    cross_key = gap, low, high, cross_word
                    note_transition(layer, "cross_anchor_transition", cross,
                                    cross_key, output, record, n, lower, gap)
                    layer["cross_anchor_transition_observations"] += 1
                    if not parent_facts.has_strong_five:
                        layer["cross_anchor_open_transition_observations"] += 1
                        note_transition(layer, "cross_anchor_open_transition", cross_open,
                                        cross_key, output, record, n, lower, gap)

                    all_key = (
                        gap, low, high, lower_facts.by_gap[:n + 1],
                        upper_facts.by_gap[:n + 1],
                    )
                    note_transition(layer, "all_gap_transition", all_gap,
                                    all_key, output, record, n, lower, gap)
                    layer["all_gap_transition_observations"] += 1
                    if not parent_facts.has_strong_five:
                        layer["all_gap_open_transition_observations"] += 1
                        note_transition(layer, "all_gap_open_transition", all_gap_open,
                                        all_key, output, record, n, lower, gap)

                for anchor in range(n):
                    if lower & (1 << anchor):
                        sibling = upper_facts
                        side = "lower"
                    else:
                        sibling = lower_facts
                        side = "upper"
                    for kind, chains in (("cup", sibling.four_cups),
                                         ("cap", sibling.four_caps)):
                        for chain in chains:
                            status = anchor_relation(chain, anchor)
                            feed(anchor_hash, (
                                "A", n, f"{parent:x}", f"{lower:x}", anchor,
                                side, kind, f"{chain:x}", status,
                            ))
                            layer["context_record_count"] += 1
                            layer["singleton_context_record_count"] += int(singleton)
                            layer["context_relation_histogram"][f"{side},{kind},{status}"] += 1
                            relevant = (side == "upper" and kind == "cup") or (
                                side == "lower" and kind == "cap")
                            if not relevant:
                                continue
                            extension = check.supported_triples(chain | (1 << anchor))
                            actual = parent & extension == (extension if kind == "cup" else 0)
                            endpoint = status != "S"
                            layer["endpoint_transition_checks"] += 1
                            layer["endpoint_transition_violations"] += int(actual != endpoint)
                            forbidden = not (
                                parent_facts.has_cup_five if kind == "cup"
                                else parent_facts.has_cap_five
                            )
                            if forbidden:
                                layer["saturation_checks"] += 1
                                layer["saturation_violations"] += int(status != "S")

            layer["local_transition_input_count"] += len(local)
            layer["local_open_transition_input_count"] += len(local_open)
            layer["cross_anchor_transition_input_count"] += len(cross)
            layer["cross_anchor_open_transition_input_count"] += len(cross_open)
            layer["all_gap_transition_input_count"] += len(all_gap)
            layer["all_gap_open_transition_input_count"] += len(all_gap_open)

        layer["context_relation_histogram"] = dict(
            sorted(layer["context_relation_histogram"].items()))
        layers[str(n)] = layer

    alphabet_text = "".join(
        ",".join(map(str, profile)) + "\n"
        for profile in sorted(decode_profile(code) for code in alphabet)
    ).encode()
    return {
        "profile": {
            "alphabet_size": len(alphabet),
            "alphabet_sha256": hashlib.sha256(alphabet_text).hexdigest(),
        },
        "canonical_hashes": {
            "coloring_records_sha256": coloring_hash.hexdigest(),
            "root_records_sha256": root_hash.hexdigest(),
            "anchor_chain_records_sha256": anchor_hash.hexdigest(),
        },
        "layers": layers,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported manifest schema")
    maximum_n = manifest.get("maximum_n")
    if not isinstance(maximum_n, int) or not 1 <= maximum_n <= 8:
        parser.error("maximum_n must lie between 1 and 8")
    actual = replay(maximum_n)
    expected_profile = {
        key: manifest["profile"][key] for key in ("alphabet_size", "alphabet_sha256")
    }
    checks = {
        "profile_alphabet": actual["profile"] == expected_profile,
        "canonical_hashes": actual["canonical_hashes"] == manifest["canonical_hashes"],
        "layers": actual["layers"] == manifest["layers"],
    }
    result = {
        "manifest": str(args.manifest),
        "maximum_n": maximum_n,
        "checks": checks,
        "ok": all(checks.values()),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
