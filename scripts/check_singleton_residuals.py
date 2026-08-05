#!/usr/bin/env python3
"""Independently replay a singleton-context residual-oracle manifest.

This checker imports no producer code.  It regenerates decomposable colorings
with a memoized recursive recurrence, evaluates strong sets and anchored chain
profiles directly, reconstructs all singleton contexts, and recomputes every
class statistic and canonical digest in the compact manifest.
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
    def __init__(self, child_size: int, strong_size: int):
        self.child_size = child_size
        self.parent_size = child_size + 1
        self.strong_size = strong_size
        self.child_triples = all_triples(child_size)
        self.child_positions = {
            triple: index for index, triple in enumerate(self.child_triples)
        }

    @functools.cache
    def supported(self, mask: int) -> int:
        answer = 0
        for index, triple in enumerate(self.child_triples):
            if all(mask & (1 << vertex) for vertex in triple):
                answer |= 1 << index
        return answer

    def root_fixed(self, mask: int, lower: int) -> int:
        answer = 0
        for index, (a, b, c) in enumerate(self.child_triples):
            selected = (1 << a) | (1 << b) | (1 << c)
            if selected & mask != selected:
                continue
            pieces = (selected & lower).bit_count()
            if pieces in (1, 2) and lower & (1 << b):
                answer |= 1 << index
        return answer

    @functools.cache
    def colorings(self, mask: int) -> tuple[int, ...]:
        if mask.bit_count() == 1:
            return (0,)
        values = set()
        for lower in submasks(mask):
            upper = mask ^ lower
            fixed = self.root_fixed(mask, lower)
            for left in self.colorings(lower):
                for right in self.colorings(upper):
                    values.add(left | right | fixed)
        return tuple(sorted(values))

    def normalized_colorings(self) -> tuple[int, ...]:
        return self.colorings((1 << self.child_size) - 1)


@functools.cache
def observation_spec(n: int, k: int):
    positions = {triple: index for index, triple in enumerate(all_triples(n))}
    chains = []
    strong = []
    for size in range(1, min(n, k) + 1):
        for vertices in itertools.combinations(range(n), size):
            required = sum(
                1 << positions[triple]
                for triple in itertools.combinations(vertices, 3)
            )
            item = (size, vertices[0], vertices[-1], required)
            chains.append(item)
            if size == k:
                comparisons = []
                for a, b, c, d in itertools.combinations(vertices, 4):
                    comparisons.append((positions[(a, b, c)], positions[(a, b, d)]))
                    comparisons.append((positions[(a, c, d)], positions[(b, c, d)]))
                strong.append(tuple(comparisons))
    return tuple(chains), tuple(strong)


def observe(n: int, k: int, bits: int) -> bytes:
    chains, strong_sets = observation_spec(n, k)
    for comparisons in strong_sets:
        if all(bool(bits & (1 << left)) == bool(bits & (1 << right))
               for left, right in comparisons):
            return bytes((1,)) + bytes(4 * (n + 1))
    maxima = [[0] * 6 for _ in range(n + 1)]
    for size, first, last, required in chains:
        cup = bits & required == required
        cap = bits & required == 0
        if not cup and not cap:
            continue
        for gap in range(n + 1):
            place = 0 if gap <= first else 1 if gap > last else 2
            if cup:
                maxima[gap][place] = max(maxima[gap][place], size)
            if cap:
                maxima[gap][3 + place] = max(maxima[gap][3 + place], size)
    result = bytearray((0,))
    for row in maxima:
        word = sum(value << (3 * index) for index, value in enumerate(row))
        result.extend(struct.pack("<I", word))
    return bytes(result)


def insert_child(bits: int, child_n: int, root: int) -> int:
    child_triples = all_triples(child_n)
    parent_positions = {
        triple: index for index, triple in enumerate(all_triples(child_n + 1))
    }
    answer = 0
    for index, triple in enumerate(child_triples):
        if not bits & (1 << index):
            continue
        image = tuple(vertex if vertex < root else vertex + 1 for vertex in triple)
        answer |= 1 << parent_positions[image]
    return answer


def parent_crossing(n: int, lower: int) -> int:
    answer = 0
    for index, (a, b, c) in enumerate(all_triples(n)):
        chosen = (1 << a) | (1 << b) | (1 << c)
        count = (chosen & lower).bit_count()
        if count in (1, 2) and lower & (1 << b):
            answer |= 1 << index
    return answer


_REPLAY_COLORINGS: tuple[int, ...] = ()
_REPLAY_CHILD_N = 0
_REPLAY_K = 0


def init_context_worker(colorings: tuple[int, ...], child_n: int, k: int) -> None:
    global _REPLAY_COLORINGS, _REPLAY_CHILD_N, _REPLAY_K
    _REPLAY_COLORINGS = colorings
    _REPLAY_CHILD_N = child_n
    _REPLAY_K = k


def replay_context(context: tuple[int, str]) -> tuple[dict[str, object], bytes]:
    root, role = context
    n = _REPLAY_CHILD_N + 1
    root_mask = 1 << root
    lower = root_mask if role == "upper" else ((1 << n) - 1) ^ root_mask
    fixed = parent_crossing(n, lower)
    output = bytearray()
    digest = hashlib.sha256()
    closed = 0
    for child in _REPLAY_COLORINGS:
        record = observe(n, _REPLAY_K, insert_child(child, _REPLAY_CHILD_N, root) | fixed)
        output.extend(record)
        digest.update(record)
        closed += record[0]
    metadata = {
        "root": root,
        "child_role": role,
        "lower_mask_hex": f"{lower:x}",
        "record_count": len(_REPLAY_COLORINGS),
        "record_size": 1 + 4 * (n + 1),
        "closed_count": closed,
        "open_count": len(_REPLAY_COLORINGS) - closed,
        "records_sha256": digest.hexdigest(),
    }
    return metadata, bytes(output)


def split_records(blob: bytes, size: int) -> list[bytes]:
    if len(blob) % size:
        raise ValueError("misaligned observation table")
    return [blob[start:start + size] for start in range(0, len(blob), size)]


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


def first_difference(left: int, right: int, own, tables, contexts):
    if own[left] != own[right]:
        return {
            "kind": "child_observation",
            **describe_difference(own[left], own[right]),
        }
    for metadata, records in zip(contexts, tables):
        if records[left] != records[right]:
            return {
                "kind": "singleton_context",
                "root": metadata["root"],
                "child_role": metadata["child_role"],
                **describe_difference(records[left], records[right]),
            }
    return None


def profile_values(word: int) -> list[int]:
    return [(word >> (3 * coordinate)) & 7 for coordinate in range(6)]


def describe_difference(left: bytes, right: bytes) -> dict[str, object]:
    result: dict[str, object] = {
        "left_closed": bool(left[0]),
        "right_closed": bool(right[0]),
    }
    if left[0] != right[0] or left[0]:
        return result
    names = (
        "cup_anchor_left",
        "cup_anchor_right",
        "cup_straddled",
        "cap_anchor_left",
        "cap_anchor_right",
        "cap_straddled",
    )
    gap_count = (len(left) - 1) // 4
    for gap in range(gap_count):
        offset = 1 + 4 * gap
        first = struct.unpack("<I", left[offset:offset + 4])[0]
        second = struct.unpack("<I", right[offset:offset + 4])[0]
        if first != second:
            a = profile_values(first)
            b = profile_values(second)
            result["gap"] = gap
            result["fields"] = [name for name, x, y in zip(names, a, b) if x != y]
            result["left_profile"] = a
            result["right_profile"] = b
            return result
    raise AssertionError("different open records agreed at every gap")


def refinement_counts(own, tables, contexts) -> dict[str, object]:
    individual = [
        {
            "root": metadata["root"],
            "child_role": metadata["child_role"],
            "class_count": len(set(zip(own, records))),
        }
        for metadata, records in zip(contexts, tables)
    ]
    signatures = own
    available = list(range(len(tables)))
    greedy = []
    old_count = len(set(signatures))
    while available:
        ranked = [
            (len(set(zip(signatures, tables[index]))), -index, index)
            for index in available
        ]
        new_count, _, chosen = max(ranked)
        if new_count == old_count:
            break
        metadata = contexts[chosen]
        greedy.append({
            "root": metadata["root"],
            "child_role": metadata["child_role"],
            "class_count": new_count,
        })
        signatures = [a + b for a, b in zip(signatures, tables[chosen])]
        available.remove(chosen)
        old_count = new_count
    return {
        "individual_contexts": individual,
        "greedy_context_sequence": greedy,
        "redundant_context_count_after_greedy": len(available),
    }


def summarize(repo: Path, child_n: int, k: int, colorings, contexts, blobs):
    own = [observe(child_n, k, bits) for bits in colorings]
    tables = [
        split_records(blob, int(metadata["record_size"]))
        for metadata, blob in zip(contexts, blobs)
    ]
    class_by_signature = {}
    sizes = Counter()
    first_member = {}
    second_member = {}
    class_ids = []
    own_first = {}
    first_refinement = None
    coloring_hash = hashlib.sha256()
    state_hash = hashlib.sha256()
    for index, bits in enumerate(colorings):
        signature = own[index] + b"".join(table[index] for table in tables)
        class_id = class_by_signature.get(signature)
        if class_id is None:
            class_id = len(class_by_signature)
            class_by_signature[signature] = class_id
            first_member[class_id] = bits
        elif class_id not in second_member:
            second_member[class_id] = bits
        class_ids.append(class_id)
        sizes[class_id] += 1
        coloring_hash.update(f"{bits:x}\n".encode())
        state_hash.update(f"{bits:x}|{class_id}|".encode())
        state_hash.update(hashlib.sha256(signature).digest())
        previous = own_first.get(own[index])
        if previous is None:
            own_first[own[index]] = index, class_id
        elif previous[1] != class_id and first_refinement is None:
            first_refinement = {
                "left_coloring_hex": f"{colorings[previous[0]]:x}",
                "right_coloring_hex": f"{bits:x}",
                "first_difference": first_difference(
                    previous[0], index, own, tables, contexts
                ),
            }
    by_bits = {bits: index for index, bits in enumerate(colorings)}
    regressions = {}
    for label, pair in regression_pairs(repo, child_n).items():
        left, right = (by_bits[value] for value in pair)
        regressions[label] = {
            "left_coloring_hex": f"{pair[0]:x}",
            "right_coloring_hex": f"{pair[1]:x}",
            "equal_child_observation": own[left] == own[right],
            "equal_residual_state": class_ids[left] == class_ids[right],
            "first_difference": first_difference(left, right, own, tables, contexts),
        }
    positive = None
    if second_member:
        class_id = min(second_member)
        positive = {
            "class_id": class_id,
            "left_coloring_hex": f"{first_member[class_id]:x}",
            "right_coloring_hex": f"{second_member[class_id]:x}",
        }
    histogram = Counter(sizes.values())
    return {
        "coloring_count": len(colorings),
        "colorings_sha256": coloring_hash.hexdigest(),
        "child_observation_count": len(set(own)),
        "residual_class_count": len(class_by_signature),
        "nontrivial_residual_class_count": sum(value > 1 for value in sizes.values()),
        "largest_residual_class_size": max(sizes.values(), default=0),
        "residual_class_size_histogram": {
            str(size): count for size, count in sorted(histogram.items())
        },
        "state_records_sha256": state_hash.hexdigest(),
        "context_refinement": refinement_counts(own, tables, contexts),
        "first_context_refinement": first_refinement,
        "first_nontrivial_residual_class": positive,
        "regressions": regressions,
    }


def replay(manifest: dict[str, object], workers: int) -> dict[str, object]:
    parameters = manifest["parameters"]
    child_n = int(parameters["child_size"])
    k = int(parameters["strong_size"])
    repo = Path(__file__).resolve().parent.parent
    colorings = Replay(child_n, k).normalized_colorings()
    requested = [
        (root, role)
        for root in range(child_n + 1)
        for role in ("lower", "upper")
    ]
    init_context_worker(colorings, child_n, k)
    if workers == 1:
        results = [replay_context(context) for context in requested]
    else:
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=workers,
            initializer=init_context_worker,
            initargs=(colorings, child_n, k),
        ) as pool:
            results = list(pool.map(replay_context, requested))
    results.sort(key=lambda value: (int(value[0]["root"]), str(value[0]["child_role"])))
    contexts = [metadata for metadata, _ in results]
    blobs = [blob for _, blob in results]
    return {
        "contexts": contexts,
        "summary": summarize(repo, child_n, k, colorings, contexts, blobs),
    }


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
    expected_contexts = [
        {key: value for key, value in item.items() if key != "machine_file"}
        for item in manifest["contexts"]
    ]
    repo = Path(__file__).resolve().parent.parent
    source_checks = {
        label: file_sha256(repo / metadata["path"]) == metadata["sha256"]
        for label, metadata in manifest["sources"].items()
    }
    checks = {
        "source_hashes": all(source_checks.values()),
        "contexts": actual["contexts"] == expected_contexts,
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
