#!/usr/bin/env python3
"""Independently replay a span-rank singleton-congruence manifest.

This checker imports no producer module.  It regenerates decomposable
colorings, recomputes every endpoint-span rank and singleton parent directly,
and compares all counts, collision witnesses, and canonical digests with the
compact checked-in manifest.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import functools
import hashlib
import itertools
import json
import os
import struct
from collections import Counter
from pathlib import Path


def all_triples(n: int) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(range(n), 3))


def submasks(mask: int):
    value = (mask - 1) & mask
    while value:
        yield value
        value = (value - 1) & mask


class Replay:
    def __init__(self, size: int):
        self.size = size
        self.triples = all_triples(size)

    def fixed_crossing(self, mask: int, lower: int) -> int:
        answer = 0
        for index, triple in enumerate(self.triples):
            selected = sum(1 << vertex for vertex in triple)
            if selected & mask != selected:
                continue
            lower_count = (selected & lower).bit_count()
            if lower_count in (1, 2) and lower & (1 << triple[1]):
                answer |= 1 << index
        return answer

    @functools.cache
    def colorings(self, mask: int) -> tuple[int, ...]:
        if mask.bit_count() == 1:
            return (0,)
        values = set()
        for lower in submasks(mask):
            upper = mask ^ lower
            fixed = self.fixed_crossing(mask, lower)
            for left in self.colorings(lower):
                for right in self.colorings(upper):
                    values.add(left | right | fixed)
        return tuple(sorted(values))

    def normalized_colorings(self) -> tuple[int, ...]:
        return self.colorings((1 << self.size) - 1)


@functools.cache
def specifications(n: int, k: int):
    triples = all_triples(n)
    positions = {triple: index for index, triple in enumerate(triples)}
    pairs = tuple(itertools.combinations(range(n), 2))
    pair_positions = {pair: index for index, pair in enumerate(pairs)}
    chains = []
    for size in range(2, min(n, k - 1) + 1):
        for vertices in itertools.combinations(range(n), size):
            chain_positions = tuple(
                positions[triple]
                for triple in itertools.combinations(vertices, 3)
            )
            chains.append(
                (size, pair_positions[(vertices[0], vertices[-1])], chain_positions)
            )
    strong = []
    if k <= n:
        for vertices in itertools.combinations(range(n), k):
            comparisons = []
            for a, b, c, d in itertools.combinations(vertices, 4):
                comparisons.append((positions[(a, b, c)], positions[(a, b, d)]))
                comparisons.append((positions[(a, c, d)], positions[(b, c, d)]))
            strong.append(tuple(comparisons))
    return pairs, tuple(chains), tuple(strong)


def contains_strong(n: int, k: int, bits: int) -> bool:
    _, _, strong_sets = specifications(n, k)
    return any(
        all(
            bool(bits & (1 << left)) == bool(bits & (1 << right))
            for left, right in comparisons
        )
        for comparisons in strong_sets
    )


@functools.cache
def observation_chains(n: int, k: int):
    positions = {triple: index for index, triple in enumerate(all_triples(n))}
    chains = []
    for size in range(1, min(n, k) + 1):
        for vertices in itertools.combinations(range(n), size):
            required = sum(
                1 << positions[triple]
                for triple in itertools.combinations(vertices, 3)
            )
            chains.append((size, vertices[0], vertices[-1], required))
    return tuple(chains)


def span_footprint(n: int, k: int, bits: int) -> bytes:
    pairs, chains, _ = specifications(n, k)
    if contains_strong(n, k, bits):
        return bytes((1,)) + bytes(len(pairs))
    cup = [0] * len(pairs)
    cap = [0] * len(pairs)
    for size, pair_index, chain_positions in chains:
        colors = tuple(bool(bits & (1 << position)) for position in chain_positions)
        if all(colors):
            cup[pair_index] = max(cup[pair_index], size)
        if not any(colors):
            cap[pair_index] = max(cap[pair_index], size)
    return bytes((0,)) + bytes(
        cup_rank | (cap_rank << 4)
        for cup_rank, cap_rank in zip(cup, cap)
    )


def direct_observation(n: int, k: int, bits: int) -> bytes:
    if contains_strong(n, k, bits):
        return bytes((1,)) + bytes(4 * (n + 1))
    maxima = [[0] * 6 for _ in range(n + 1)]
    for size, first, last, required in observation_chains(n, k):
        cup = bits & required == required
        cap = bits & required == 0
        if not cup and not cap:
            continue
        for gap in range(n + 1):
            relation = 0 if gap <= first else 1 if gap > last else 2
            if cup:
                maxima[gap][relation] = max(maxima[gap][relation], size)
            if cap:
                maxima[gap][3 + relation] = max(maxima[gap][3 + relation], size)
    result = bytearray((0,))
    for row in maxima:
        word = sum(value << (3 * coordinate) for coordinate, value in enumerate(row))
        result.extend(struct.pack("<I", word))
    return bytes(result)


def footprint_observation(n: int, record: bytes) -> bytes:
    if record[0]:
        return bytes((1,)) + bytes(4 * (n + 1))
    maxima = [[0] * 6 for _ in range(n + 1)]
    for vertex in range(n):
        for gap in range(n + 1):
            relation = 0 if gap <= vertex else 1
            maxima[gap][relation] = max(maxima[gap][relation], 1)
            maxima[gap][3 + relation] = max(maxima[gap][3 + relation], 1)
    pairs, _, _ = specifications(n, 4)
    for index, (first, last) in enumerate(pairs):
        code = record[1 + index]
        cup = code & 15
        cap = code >> 4
        for gap in range(n + 1):
            relation = 0 if gap <= first else 1 if gap > last else 2
            maxima[gap][relation] = max(maxima[gap][relation], cup)
            maxima[gap][3 + relation] = max(maxima[gap][3 + relation], cap)
    result = bytearray((0,))
    for row in maxima:
        word = sum(value << (3 * coordinate) for coordinate, value in enumerate(row))
        result.extend(struct.pack("<I", word))
    return bytes(result)


def insert_child(bits: int, child_n: int, root: int) -> int:
    child_triples = all_triples(child_n)
    parent_positions = {
        triple: index for index, triple in enumerate(all_triples(child_n + 1))
    }
    answer = 0
    for index, triple in enumerate(child_triples):
        if bits & (1 << index):
            image = tuple(vertex if vertex < root else vertex + 1 for vertex in triple)
            answer |= 1 << parent_positions[image]
    return answer


def parent_crossing(n: int, lower: int) -> int:
    answer = 0
    for index, triple in enumerate(all_triples(n)):
        selected = sum(1 << vertex for vertex in triple)
        count = (selected & lower).bit_count()
        if count in (1, 2) and lower & (1 << triple[1]):
            answer |= 1 << index
    return answer


_COLORINGS: tuple[int, ...] = ()
_CHILD_STATES: tuple[bytes, ...] = ()
_CHILD_N = 0
_K = 0


def initialize_worker(
    colorings: tuple[int, ...], child_states: tuple[bytes, ...], child_n: int, k: int
) -> None:
    global _COLORINGS, _CHILD_STATES, _CHILD_N, _K
    _COLORINGS = colorings
    _CHILD_STATES = child_states
    _CHILD_N = child_n
    _K = k


def replay_context(context: tuple[int, str]) -> dict[str, object]:
    root, role = context
    parent_n = _CHILD_N + 1
    singleton = 1 << root
    lower = singleton if role == "upper" else ((1 << parent_n) - 1) ^ singleton
    fixed = parent_crossing(parent_n, lower)
    digest = hashlib.sha256()
    seen = {}
    collisions = 0
    first_collision = None
    readout_mismatches = 0
    parent_states = set()
    for index, child_bits in enumerate(_COLORINGS):
        parent_bits = insert_child(child_bits, _CHILD_N, root) | fixed
        parent_state = span_footprint(parent_n, _K, parent_bits)
        parent_states.add(parent_state)
        digest.update(parent_state)
        if footprint_observation(parent_n, parent_state) != direct_observation(
            parent_n, _K, parent_bits
        ):
            readout_mismatches += 1
        child_state = _CHILD_STATES[index]
        previous = seen.get(child_state)
        if previous is None:
            seen[child_state] = parent_state, child_bits, parent_bits
        elif previous[0] != parent_state:
            collisions += 1
            if first_collision is None:
                first_collision = {
                    "first_child_hex": f"{previous[1]:x}",
                    "second_child_hex": f"{child_bits:x}",
                    "first_parent_hex": f"{previous[2]:x}",
                    "second_parent_hex": f"{parent_bits:x}",
                }
    return {
        "root": root,
        "child_role": role,
        "lower_mask_hex": f"{lower:x}",
        "record_count": len(_COLORINGS),
        "record_size": 1 + len(tuple(itertools.combinations(range(parent_n), 2))),
        "child_state_count": len(seen),
        "parent_state_count": len(parent_states),
        "transition_collision_count": collisions,
        "first_transition_collision": first_collision,
        "observation_readout_mismatch_count": readout_mismatches,
        "records_sha256": digest.hexdigest(),
    }


def normalize_certificate_child(hex_bits: str, root: int, child_n: int) -> int:
    ambient = int(hex_bits, 16)
    ambient_positions = {
        triple: index for index, triple in enumerate(all_triples(child_n + 1))
    }
    answer = 0
    for index, triple in enumerate(all_triples(child_n)):
        image = tuple(vertex if vertex < root else vertex + 1 for vertex in triple)
        if ambient & (1 << ambient_positions[image]):
            answer |= 1 << index
    return answer


def regression_pairs(repo: Path, child_n: int) -> dict[str, tuple[int, int]]:
    if child_n != 8:
        return {}
    context = json.loads(
        (repo / "data/derived/e3-context-k6-n9-singleton-collision.json").read_text()
    )
    rank = json.loads((repo / "data/derived/e3-rank-k6-n9-singleton.json").read_text())
    collision = rank["pair_rank_collision"]
    return {
        "all_gap_collision": tuple(
            normalize_certificate_child(context[side]["upper_coloring_hex"], 1, child_n)
            for side in ("left", "right")
        ),
        "pair_rank_collision": tuple(
            normalize_certificate_child(collision[side]["upper_coloring_hex"], 1, child_n)
            for side in ("left", "right")
        ),
    }


def summarize(
    repo: Path,
    colorings: tuple[int, ...],
    states: tuple[bytes, ...],
    child_n: int,
    contexts: list[dict[str, object]],
) -> dict[str, object]:
    classes = {}
    sizes = Counter()
    first = {}
    second = {}
    state_digest = hashlib.sha256()
    for bits, state in zip(colorings, states):
        class_id = classes.get(state)
        if class_id is None:
            class_id = len(classes)
            classes[state] = class_id
            first[class_id] = bits
        elif class_id not in second:
            second[class_id] = bits
        sizes[class_id] += 1
        state_digest.update(f"{bits:x}|{class_id}|".encode())
        state_digest.update(hashlib.sha256(state).digest())
    positive = None
    if second:
        class_id = min(second)
        positive = {
            "class_id": class_id,
            "left_coloring_hex": f"{first[class_id]:x}",
            "right_coloring_hex": f"{second[class_id]:x}",
        }
    index_by_bits = {bits: index for index, bits in enumerate(colorings)}
    regressions = {}
    for label, pair in regression_pairs(repo, child_n).items():
        left, right = (states[index_by_bits[bits]] for bits in pair)
        regressions[label] = {
            "left_coloring_hex": f"{pair[0]:x}",
            "right_coloring_hex": f"{pair[1]:x}",
            "equal_child_footprint": left == right,
        }
    histogram = Counter(sizes.values())
    return {
        "coloring_count": len(colorings),
        "child_footprint_count": len(classes),
        "nontrivial_child_footprint_count": sum(size > 1 for size in sizes.values()),
        "largest_child_footprint_size": max(sizes.values(), default=0),
        "child_footprint_size_histogram": {
            str(size): count for size, count in sorted(histogram.items())
        },
        "child_state_records_sha256": state_digest.hexdigest(),
        "first_nontrivial_child_footprint": positive,
        "total_transition_collision_count": sum(
            int(context["transition_collision_count"]) for context in contexts
        ),
        "total_observation_readout_mismatch_count": sum(
            int(context["observation_readout_mismatch_count"]) for context in contexts
        ),
        "regressions": regressions,
    }


def replay(manifest: dict[str, object], workers: int) -> dict[str, object]:
    parameters = manifest["parameters"]
    child_n = int(parameters["child_size"])
    k = int(parameters["strong_size"])
    repo = Path(__file__).resolve().parent.parent
    colorings = Replay(child_n).normalized_colorings()
    states = tuple(span_footprint(child_n, k, bits) for bits in colorings)
    child_mismatches = sum(
        footprint_observation(child_n, state) != direct_observation(child_n, k, bits)
        for bits, state in zip(colorings, states)
    )
    requested = [
        (root, role)
        for root in range(child_n + 1)
        for role in ("lower", "upper")
    ]
    initialize_worker(colorings, states, child_n, k)
    if workers == 1:
        contexts = [replay_context(context) for context in requested]
    else:
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=workers,
            initializer=initialize_worker,
            initargs=(colorings, states, child_n, k),
        ) as pool:
            contexts = list(pool.map(replay_context, requested))
    contexts.sort(key=lambda item: (int(item["root"]), str(item["child_role"])))
    summary = summarize(repo, colorings, states, child_n, contexts)
    summary["child_observation_readout_mismatch_count"] = child_mismatches
    return {"contexts": contexts, "summary": summary}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--workers", type=int, default=min(8, os.cpu_count() or 1))
    args = parser.parse_args()
    if not 1 <= args.workers <= 8:
        parser.error("workers must lie between 1 and 8")
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported manifest schema")
    actual = replay(manifest, args.workers)
    repo = Path(__file__).resolve().parent.parent
    source_checks = {
        label: file_sha256(repo / metadata["path"]) == metadata["sha256"]
        for label, metadata in manifest["sources"].items()
    }
    checks = {
        "source_hashes": all(source_checks.values()),
        "contexts": actual["contexts"] == manifest["contexts"],
        "summary": actual["summary"] == manifest["summary"],
    }
    result = {
        "manifest": str(args.manifest),
        "source_checks": source_checks,
        "checks": checks,
        "ok": all(checks.values()),
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
