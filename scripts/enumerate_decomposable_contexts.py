#!/usr/bin/env python3
"""Produce the exact all-root k=5 context-profile census.

The experiment ranges over every recursively deep-below coloring on at most
eight ordered leaves and every root split that induces that coloring.  It is
deliberately separate from ``enumerate_decomposable_colorings.py``: that
producer retains one witness tree per coloring, whereas this census must keep
all compatible roots.

An external anchor is represented by a sweep gap ``g``.  For cups and caps we
record the largest chain, clipped at five, in each relation to the anchor:
the anchor is left of the chain, right of the chain, or strictly straddled by
the chain.  A final bit records a strong five-set.  The independent checker
does not import this module.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import subprocess
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


PROFILE_FIELDS = (
    "cup_anchor_left",
    "cup_anchor_right",
    "cup_straddled",
    "cap_anchor_left",
    "cap_anchor_right",
    "cap_straddled",
)
PROFILE_CLIP = 5


def triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def nonempty_submasks(mask: int):
    sub = mask
    while sub:
        yield sub
        sub = (sub - 1) & mask


def pack_profile(values: list[int], strong_five: bool) -> int:
    answer = int(strong_five) << 18
    for index, value in enumerate(values):
        answer |= value << (3 * index)
    return answer


def unpack_profile(profile: int) -> tuple[int, ...]:
    return tuple((profile >> (3 * index)) & 7 for index in range(6)) + (
        (profile >> 18) & 1,
    )


def profile_le(left: int, right: int) -> bool:
    a = unpack_profile(left)
    b = unpack_profile(right)
    return all(x <= y for x, y in zip(a[:6], b[:6])) and a[6] <= b[6]


@dataclass(frozen=True)
class ChainData:
    profiles: tuple[int, ...]
    cups_four: tuple[int, ...]
    caps_four: tuple[int, ...]
    cup_five: bool
    cap_five: bool
    strong_five: bool
    signotope: bool


class Census:
    def __init__(self, maximum_n: int):
        self.maximum_n = maximum_n
        self.triple_list = triples(maximum_n)
        self.positions = {triple: index for index, triple in enumerate(self.triple_list)}
        self.triple_masks: dict[int, int] = {}
        self.subsets_by_mask: dict[int, tuple[tuple[int, int, int, int], ...]] = {}
        self.states: dict[int, frozenset[int]] = {}
        self.analysis_cache: dict[tuple[int, int], ChainData] = {}
        full = (1 << maximum_n) - 1
        for mask in range(1, full + 1):
            triple_bits = 0
            for index, triple in enumerate(self.triple_list):
                selected = sum(1 << vertex for vertex in triple)
                if selected & mask == selected:
                    triple_bits |= 1 << index
            self.triple_masks[mask] = triple_bits
            chain_subsets: list[tuple[int, int, int, int]] = []
            for subset in nonempty_submasks(mask):
                size = subset.bit_count()
                if size <= PROFILE_CLIP:
                    vertices = tuple(i for i in range(maximum_n) if subset & (1 << i))
                    chain_subsets.append((subset, size, vertices[0], vertices[-1]))
            self.subsets_by_mask[mask] = tuple(chain_subsets)

    def crossing_bits(self, mask: int, lower: int) -> int:
        answer = 0
        for index, (i, j, k) in enumerate(self.triple_list):
            selected = (1 << i) | (1 << j) | (1 << k)
            if selected & mask != selected:
                continue
            count = (selected & lower).bit_count()
            if 0 < count < 3 and lower & (1 << j):
                answer |= 1 << index
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
                answers: set[int] = set()
                for lower in nonempty_submasks(mask):
                    if lower == mask:
                        continue
                    upper = mask ^ lower
                    fixed = self.crossing_bits(mask, lower)
                    for lower_bits in self.states[lower]:
                        for upper_bits in self.states[upper]:
                            answers.add(lower_bits | upper_bits | fixed)
                self.states[mask] = frozenset(answers)

    def is_strong_five(self, bits: int, subset: int) -> bool:
        vertices = tuple(i for i in range(self.maximum_n) if subset & (1 << i))
        for a, b, c, d in itertools.combinations(vertices, 4):
            abc = bool(bits & (1 << self.positions[(a, b, c)]))
            abd = bool(bits & (1 << self.positions[(a, b, d)]))
            acd = bool(bits & (1 << self.positions[(a, c, d)]))
            bcd = bool(bits & (1 << self.positions[(b, c, d)]))
            if abc != abd or acd != bcd:
                return False
        return True

    def is_signotope(self, bits: int, mask: int) -> bool:
        vertices = tuple(i for i in range(self.maximum_n) if mask & (1 << i))
        for a, b, c, d in itertools.combinations(vertices, 4):
            sequence = (
                bool(bits & (1 << self.positions[(a, b, c)])),
                bool(bits & (1 << self.positions[(a, b, d)])),
                bool(bits & (1 << self.positions[(a, c, d)])),
                bool(bits & (1 << self.positions[(b, c, d)])),
            )
            if sum(x != y for x, y in zip(sequence, sequence[1:])) > 1:
                return False
        return True

    def analyze(self, mask: int, bits: int) -> ChainData:
        key = mask, bits
        cached = self.analysis_cache.get(key)
        if cached is not None:
            return cached
        values = [[0] * 6 for _ in range(self.maximum_n + 1)]
        cups_four: list[int] = []
        caps_four: list[int] = []
        cup_five = False
        cap_five = False
        strong_five = False
        for subset, size, minimum, maximum in self.subsets_by_mask[mask]:
            required = self.triple_masks[subset]
            is_cup = bits & required == required
            is_cap = bits & required == 0
            if size == 4:
                if is_cup:
                    cups_four.append(subset)
                if is_cap:
                    caps_four.append(subset)
            if size == 5:
                cup_five |= is_cup
                cap_five |= is_cap
                strong_five |= self.is_strong_five(bits, subset)
            if not is_cup and not is_cap:
                continue
            for gap in range(self.maximum_n + 1):
                relation = 0 if gap <= minimum else 1 if gap > maximum else 2
                if is_cup:
                    values[gap][relation] = max(values[gap][relation], size)
                if is_cap:
                    values[gap][3 + relation] = max(values[gap][3 + relation], size)
        profiles = tuple(pack_profile(value, strong_five) for value in values)
        answer = ChainData(
            profiles=profiles,
            cups_four=tuple(sorted(cups_four)),
            caps_four=tuple(sorted(caps_four)),
            cup_five=cup_five,
            cap_five=cap_five,
            strong_five=strong_five,
            signotope=self.is_signotope(bits, mask),
        )
        self.analysis_cache[key] = answer
        return answer

    def roots_for(self, mask: int, lower: int) -> list[tuple[int, int, int]]:
        upper = mask ^ lower
        fixed = self.crossing_bits(mask, lower)
        records = [
            (lower_bits | upper_bits | fixed, lower_bits, upper_bits)
            for lower_bits in self.states[lower]
            for upper_bits in self.states[upper]
        ]
        records.sort()
        if len({parent for parent, _, _ in records}) != len(records):
            raise AssertionError("child restrictions did not identify a root record")
        return records


def relation(chain: int, anchor: int) -> str:
    vertices = tuple(i for i in range(chain.bit_length()) if chain & (1 << i))
    if anchor < vertices[0]:
        return "L"
    if anchor > vertices[-1]:
        return "R"
    return "S"


def update_hash(digest, fields) -> None:
    digest.update(("|".join(map(str, fields)) + "\n").encode())


def collision_witness(
    previous: tuple[int, tuple[int, int, int, int]],
    output: int,
    record: tuple[int, int, int, int],
) -> dict[str, object]:
    old_output, old_record = previous
    return {
        "first": {
            "parent_hex": f"{old_record[0]:x}",
            "lower_bits_hex": f"{old_record[1]:x}",
            "upper_bits_hex": f"{old_record[2]:x}",
            "output_profile": list(unpack_profile(old_output)),
        },
        "second": {
            "parent_hex": f"{record[0]:x}",
            "lower_bits_hex": f"{record[1]:x}",
            "upper_bits_hex": f"{record[2]:x}",
            "output_profile": list(unpack_profile(output)),
        },
    }


def git_revision(repo: Path) -> str:
    completed = subprocess.run(
        ["git", "--git-dir=.git-data", "--work-tree=.", "rev-parse", "HEAD"],
        cwd=repo, check=True, text=True, stdout=subprocess.PIPE,
    )
    return completed.stdout.strip()


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def produce(maximum_n: int) -> dict[str, object]:
    census = Census(maximum_n)
    census.enumerate_states()
    coloring_digest = hashlib.sha256()
    root_digest = hashlib.sha256()
    context_digest = hashlib.sha256()
    aggregate_profile_alphabet: set[int] = set()
    layers: dict[str, object] = {}

    for n in range(1, maximum_n + 1):
        mask = (1 << n) - 1
        parents = sorted(census.states[mask])
        for bits in parents:
            update_hash(coloring_digest, ("C", n, f"{bits:x}"))
            aggregate_profile_alphabet.update(census.analyze(mask, bits).profiles)
        layer = {
            "distinct_coloring_count": len(parents),
            "valid_root_count": 0,
            "singleton_root_count": 0,
            "signotope_count": sum(census.analyze(mask, bits).signotope for bits in parents),
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

        for lower in range(1, mask):
            upper = mask ^ lower
            records = census.roots_for(mask, lower)
            layer["valid_root_count"] += len(records)
            if lower.bit_count() == 1 or upper.bit_count() == 1:
                layer["singleton_root_count"] += len(records)

            local_seen: dict[tuple[int, int, int], tuple[int, tuple[int, int, int, int]]] = {}
            local_open_seen: dict[tuple[int, int, int], tuple[int, tuple[int, int, int, int]]] = {}
            cross_anchor_seen: dict[tuple[object, ...], tuple[int, tuple[int, int, int, int]]] = {}
            cross_anchor_open_seen: dict[tuple[object, ...], tuple[int, tuple[int, int, int, int]]] = {}
            all_gap_seen: dict[tuple[object, ...], tuple[int, tuple[int, int, int, int]]] = {}
            all_gap_open_seen: dict[tuple[object, ...], tuple[int, tuple[int, int, int, int]]] = {}
            for parent, lower_bits, upper_bits in records:
                parent_data = census.analyze(mask, parent)
                lower_data = census.analyze(lower, lower_bits)
                upper_data = census.analyze(upper, upper_bits)
                update_hash(root_digest, (
                    "R", n, f"{parent:x}", f"{lower:x}",
                    int(parent_data.cup_five), int(parent_data.cap_five),
                    int(parent_data.strong_five), int(parent_data.signotope),
                ))
                record_id = parent, lower_bits, upper_bits, lower

                cross_word = tuple(
                    lower_data.profiles[q]
                    for q in range(n) if upper & (1 << q)
                ) + tuple(
                    upper_data.profiles[q]
                    for q in range(n) if lower & (1 << q)
                )
                for gap in range(n + 1):
                    lower_profile = lower_data.profiles[gap]
                    upper_profile = upper_data.profiles[gap]
                    output = parent_data.profiles[gap]
                    layer["restriction_checks"] += 2
                    if not profile_le(lower_profile, output):
                        layer["restriction_violations"] += 1
                    if not profile_le(upper_profile, output):
                        layer["restriction_violations"] += 1

                    local_key = gap, lower_profile, upper_profile
                    previous = local_seen.get(local_key)
                    if previous is None:
                        local_seen[local_key] = output, record_id
                    elif previous[0] != output:
                        layer["local_transition_collision_count"] += 1
                        if layer["local_transition_first_collision"] is None:
                            witness = collision_witness(previous, output, record_id)
                            witness.update({"n": n, "lower_mask_hex": f"{lower:x}", "gap": gap})
                            layer["local_transition_first_collision"] = witness
                    layer["local_transition_observations"] += 1

                    if not parent_data.strong_five:
                        layer["local_open_transition_observations"] += 1
                        previous = local_open_seen.get(local_key)
                        if previous is None:
                            local_open_seen[local_key] = output, record_id
                        elif previous[0] != output:
                            layer["local_open_transition_collision_count"] += 1
                            if layer["local_open_transition_first_collision"] is None:
                                witness = collision_witness(previous, output, record_id)
                                witness.update({"n": n, "lower_mask_hex": f"{lower:x}", "gap": gap})
                                layer["local_open_transition_first_collision"] = witness

                    cross_anchor_key = (gap, lower_profile, upper_profile, cross_word)
                    previous = cross_anchor_seen.get(cross_anchor_key)
                    if previous is None:
                        cross_anchor_seen[cross_anchor_key] = output, record_id
                    elif previous[0] != output:
                        layer["cross_anchor_transition_collision_count"] += 1
                        if layer["cross_anchor_transition_first_collision"] is None:
                            witness = collision_witness(previous, output, record_id)
                            witness.update({"n": n, "lower_mask_hex": f"{lower:x}", "gap": gap})
                            layer["cross_anchor_transition_first_collision"] = witness
                    layer["cross_anchor_transition_observations"] += 1

                    if not parent_data.strong_five:
                        layer["cross_anchor_open_transition_observations"] += 1
                        previous = cross_anchor_open_seen.get(cross_anchor_key)
                        if previous is None:
                            cross_anchor_open_seen[cross_anchor_key] = output, record_id
                        elif previous[0] != output:
                            layer["cross_anchor_open_transition_collision_count"] += 1
                            if layer["cross_anchor_open_transition_first_collision"] is None:
                                witness = collision_witness(previous, output, record_id)
                                witness.update({"n": n, "lower_mask_hex": f"{lower:x}", "gap": gap})
                                layer["cross_anchor_open_transition_first_collision"] = witness

                    all_gap_key = (
                        gap, lower_profile, upper_profile,
                        lower_data.profiles[:n + 1], upper_data.profiles[:n + 1],
                    )
                    previous = all_gap_seen.get(all_gap_key)
                    if previous is None:
                        all_gap_seen[all_gap_key] = output, record_id
                    elif previous[0] != output:
                        layer["all_gap_transition_collision_count"] += 1
                        if layer["all_gap_transition_first_collision"] is None:
                            witness = collision_witness(previous, output, record_id)
                            witness.update({"n": n, "lower_mask_hex": f"{lower:x}", "gap": gap})
                            layer["all_gap_transition_first_collision"] = witness
                    layer["all_gap_transition_observations"] += 1

                    if not parent_data.strong_five:
                        layer["all_gap_open_transition_observations"] += 1
                        previous = all_gap_open_seen.get(all_gap_key)
                        if previous is None:
                            all_gap_open_seen[all_gap_key] = output, record_id
                        elif previous[0] != output:
                            layer["all_gap_open_transition_collision_count"] += 1
                            if layer["all_gap_open_transition_first_collision"] is None:
                                witness = collision_witness(previous, output, record_id)
                                witness.update({"n": n, "lower_mask_hex": f"{lower:x}", "gap": gap})
                                layer["all_gap_open_transition_first_collision"] = witness

                for anchor in range(n):
                    if lower & (1 << anchor):
                        sibling_data = upper_data
                        side = "lower"
                    else:
                        sibling_data = lower_data
                        side = "upper"
                    for kind, chains in (("cup", sibling_data.cups_four),
                                         ("cap", sibling_data.caps_four)):
                        for chain in chains:
                            status = relation(chain, anchor)
                            update_hash(context_digest, (
                                "A", n, f"{parent:x}", f"{lower:x}", anchor,
                                side, kind, f"{chain:x}", status,
                            ))
                            layer["context_record_count"] += 1
                            if lower.bit_count() == 1 or upper.bit_count() == 1:
                                layer["singleton_context_record_count"] += 1
                            layer["context_relation_histogram"][f"{side},{kind},{status}"] += 1

                            relevant = (side == "upper" and kind == "cup") or (
                                side == "lower" and kind == "cap")
                            if relevant:
                                endpoint = status != "S"
                                extension = census.triple_masks[chain | (1 << anchor)]
                                if kind == "cup":
                                    actual = parent & extension == extension
                                else:
                                    actual = parent & extension == 0
                                layer["endpoint_transition_checks"] += 1
                                if actual != endpoint:
                                    layer["endpoint_transition_violations"] += 1
                                forbidden = not (
                                    parent_data.cup_five if kind == "cup"
                                    else parent_data.cap_five
                                )
                                if forbidden:
                                    layer["saturation_checks"] += 1
                                    if status != "S":
                                        layer["saturation_violations"] += 1

            # The dictionaries are intentionally scoped to one root word.  The
            # root membership word is structural transition input, not state.
            layer["local_transition_input_count"] += len(local_seen)
            layer["local_open_transition_input_count"] += len(local_open_seen)
            layer["cross_anchor_transition_input_count"] += len(cross_anchor_seen)
            layer["cross_anchor_open_transition_input_count"] += len(cross_anchor_open_seen)
            layer["all_gap_transition_input_count"] += len(all_gap_seen)
            layer["all_gap_open_transition_input_count"] += len(all_gap_open_seen)

        layer["context_relation_histogram"] = dict(
            sorted(layer["context_relation_histogram"].items()))
        layers[str(n)] = layer

    profile_lines = "".join(
        ",".join(map(str, values)) + "\n"
        for values in sorted(unpack_profile(profile) for profile in aggregate_profile_alphabet)
    ).encode()
    repo = Path(__file__).resolve().parent.parent
    return {
        "schema_version": 1,
        "producer": "scripts/enumerate_decomposable_contexts.py",
        "revision": git_revision(repo),
        "maximum_n": maximum_n,
        "scope": "all distinct recursive colorings and every compatible root",
        "profile": {
            "k": 5,
            "clip": PROFILE_CLIP,
            "fields": list(PROFILE_FIELDS) + ["contains_strong_five"],
            "anchor_relations": {"L": "anchor left of chain", "R": "anchor right of chain", "S": "anchor strictly straddled"},
            "alphabet_size": len(aggregate_profile_alphabet),
            "alphabet_sha256": hashlib.sha256(profile_lines).hexdigest(),
        },
        "canonical_hashes": {
            "coloring_records_sha256": coloring_digest.hexdigest(),
            "root_records_sha256": root_digest.hexdigest(),
            "anchor_chain_records_sha256": context_digest.hexdigest(),
        },
        "rational_coordinate_realizability": {
            "status": "not_attempted",
            "reason": "the abstract recursive-coloring certificates contain no coordinates",
        },
        "layers": layers,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--maximum-n", type=int, default=8)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 1 <= args.maximum_n <= 8:
        parser.error("maximum-n must lie between 1 and 8")
    manifest = produce(args.maximum_n)
    write_atomic(args.output, manifest)
    print(args.output)


if __name__ == "__main__":
    main()
