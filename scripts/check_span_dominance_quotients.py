#!/usr/bin/env python3
"""Independently replay the span-dominance incidence quotient gates.

This checker imports the prior independent raw-footprint semantics.  It
duplicates the quotient definition, recomputes every child and parent from
coloring bits, and imports neither the producer nor its quotient encoder.
"""

from __future__ import annotations

import argparse
from collections import Counter
import concurrent.futures
import hashlib
import itertools
import json
import os
from pathlib import Path

from check_span_rank_footprints import (
    Replay,
    insert_child,
    parent_crossing,
    regression_pairs,
    span_footprint,
)
from check_two_root_span_footprints import insert_child as insert_two_root_child


def frontier_bit(direction: int, color: int, rank: int, k: int) -> int:
    ranks_per_color = k - 3
    position = direction * 2 * ranks_per_color + color * ranks_per_color + rank - 3
    return 1 << position


def quotient_record(record: bytes, n: int, k: int) -> bytes:
    """Independent implementation of the candidate's canonical byte record."""
    pairs = tuple(itertools.combinations(range(n), 2))
    if len(record) != 1 + len(pairs):
        raise ValueError("record length does not match n")
    if record[0]:
        return bytes((1,))
    positions = {pair: index for index, pair in enumerate(pairs)}
    frontier = [0] * len(pairs)
    for color in range(2):
        values = tuple(
            ((label & 0x0F) if color == 0 else (label >> 4))
            for label in record[1:]
        )
        for rank in range(3, k):
            for right in range(n):
                eligible = [
                    left
                    for left in range(right)
                    if values[positions[(left, right)]] >= rank
                ]
                if eligible:
                    index = positions[(max(eligible), right)]
                    frontier[index] |= frontier_bit(0, color, rank, k)
            for left in range(n):
                eligible = [
                    right
                    for right in range(left + 1, n)
                    if values[positions[(left, right)]] >= rank
                ]
                if eligible:
                    index = positions[(left, min(eligible))]
                    frontier[index] |= frontier_bit(1, color, rank, k)

    local = [set() for _ in range(n)]
    for index, (left, right) in enumerate(pairs):
        label = record[index + 1]
        coarse = int((label & 0x0F) >= 3) + 2 * int((label >> 4) >= 3)
        if coarse:
            local[left].add((0, coarse, frontier[index]))
            local[right].add((1, coarse, frontier[index]))
    endpoint_multiset = Counter(tuple(sorted(entries)) for entries in local)

    result = bytearray([0])
    label_counts = Counter(record[1:])
    result.extend(min(k, label_counts[label]) for label in range(256))
    result.extend(len(endpoint_multiset).to_bytes(2, byteorder="little"))
    mask_bytes = (4 * (k - 3) + 7) // 8
    for endpoint_type in sorted(endpoint_multiset):
        result.append(min(k, endpoint_multiset[endpoint_type]))
        result.extend(len(endpoint_type).to_bytes(2, byteorder="little"))
        for role, coarse, mask in endpoint_type:
            result.append(role + 2 * coarse)
            result.extend(mask.to_bytes(mask_bytes, byteorder="little"))
    return bytes(result)


def update_variable_digest(digest: hashlib._Hash, record: bytes) -> None:
    digest.update(len(record).to_bytes(4, "little"))
    digest.update(record)


def state_summary(
    colorings: tuple[int, ...], raw_states: tuple[bytes, ...], states: tuple[bytes, ...]
) -> dict[str, object]:
    class_ids = {}
    class_sizes = Counter()
    raw_by_class: dict[int, dict[bytes, tuple[int, int]]] = {}
    digest = hashlib.sha256()
    for index, (bits, raw_state, state) in enumerate(zip(colorings, raw_states, states)):
        class_id = class_ids.setdefault(state, len(class_ids))
        class_sizes[class_id] += 1
        raw_by_class.setdefault(class_id, {}).setdefault(raw_state, (index, bits))
        digest.update(f"{bits:x}|{class_id}|".encode())
        update_variable_digest(digest, state)
    merged = [
        (class_id, raw_witnesses)
        for class_id, raw_witnesses in raw_by_class.items()
        if len(raw_witnesses) > 1
    ]
    first_merge = None
    if merged:
        class_id, witnesses = min(merged)
        first, second = list(witnesses.values())[:2]
        first_merge = {
            "class_id": class_id,
            "first_index": first[0],
            "second_index": second[0],
            "first_coloring_hex": f"{first[1]:x}",
            "second_coloring_hex": f"{second[1]:x}",
        }
    histogram = Counter(class_sizes.values())
    return {
        "coloring_count": len(colorings),
        "raw_footprint_count": len(set(raw_states)),
        "quotient_state_count": len(class_ids),
        "merged_raw_quotient_class_count": len(merged),
        "largest_quotient_class_size": max(class_sizes.values(), default=0),
        "quotient_class_size_histogram": {
            str(size): count for size, count in sorted(histogram.items())
        },
        "first_merged_raw_footprint": first_merge,
        "quotient_state_records_sha256": digest.hexdigest(),
    }


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


def context_result(parent_records, identity: dict[str, object]) -> dict[str, object]:
    seen = {}
    collisions = 0
    first_collision = None
    parent_states = set()
    quotient_digest = hashlib.sha256()
    cache = {}
    parent_n = _CHILD_N + (2 if "root_positions" in identity else 1)
    for index, raw_parent in enumerate(parent_records):
        parent_state = cache.get(raw_parent)
        if parent_state is None:
            parent_state = quotient_record(raw_parent, parent_n, _K)
            cache[raw_parent] = parent_state
        parent_states.add(parent_state)
        update_variable_digest(quotient_digest, parent_state)
        child_state = _CHILD_STATES[index]
        previous = seen.get(child_state)
        if previous is None:
            seen[child_state] = parent_state, index
        elif previous[0] != parent_state:
            collisions += 1
            if first_collision is None:
                first_collision = {
                    "first_child_index": previous[1],
                    "second_child_index": index,
                }
    return {
        **identity,
        "child_quotient_state_count": len(seen),
        "parent_quotient_state_count": len(parent_states),
        "transition_collision_count": collisions,
        "first_transition_collision": first_collision,
        "quotient_records_sha256": quotient_digest.hexdigest(),
    }


def singleton_context(metadata: dict[str, object]) -> dict[str, object]:
    root = int(metadata["root"])
    child_role = str(metadata["child_role"])
    parent_n = _CHILD_N + 1
    singleton = 1 << root
    lower = ((1 << parent_n) - 1) ^ singleton if child_role == "lower" else singleton
    fixed = parent_crossing(parent_n, lower)

    def parents():
        for bits in _COLORINGS:
            yield span_footprint(
                parent_n,
                _K,
                insert_child(bits, _CHILD_N, root) | fixed,
            )

    return context_result(parents(), {"root": root, "child_role": child_role})


def two_root_context(metadata: dict[str, object]) -> dict[str, object]:
    roots = tuple(int(root) for root in metadata["root_positions"])
    root_role = str(metadata["root_role"])
    parent_n = _CHILD_N + 2
    root_mask = sum(1 << root for root in roots)
    lower = root_mask if root_role == "lower" else ((1 << parent_n) - 1) ^ root_mask
    fixed = parent_crossing(parent_n, lower)

    def parents():
        for bits in _COLORINGS:
            yield span_footprint(
                parent_n,
                _K,
                insert_two_root_child(bits, _CHILD_N, roots) | fixed,
            )

    identity = {
        "root_positions": list(roots),
        "root_role": root_role,
        "child_role": metadata["child_role"],
        "interleaved": metadata["interleaved"],
    }
    return context_result(parents(), identity)


def replay_gate(
    child_n: int, k: int, requested: list[dict[str, object]], workers: int, worker
) -> dict[str, object]:
    colorings = Replay(child_n).normalized_colorings()
    raw_states = tuple(span_footprint(child_n, k, bits) for bits in colorings)
    quotient_cache = {}
    states = []
    for record in raw_states:
        state = quotient_cache.get(record)
        if state is None:
            state = quotient_record(record, child_n, k)
            quotient_cache[record] = state
        states.append(state)
    child_states = tuple(states)
    initialize_worker(colorings, child_states, child_n, k)
    if workers == 1:
        contexts = [worker(metadata) for metadata in requested]
    else:
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=workers,
            initializer=initialize_worker,
            initargs=(colorings, child_states, child_n, k),
        ) as pool:
            contexts = list(pool.map(worker, requested))
    summary = state_summary(colorings, raw_states, child_states)
    summary.update(
        {
            "context_count": len(contexts),
            "parent_transition_count": len(colorings) * len(contexts),
            "total_transition_collision_count": sum(
                int(context["transition_collision_count"]) for context in contexts
            ),
        }
    )
    if any("interleaved" in context for context in contexts):
        summary["interleaved_context_count"] = sum(
            bool(context["interleaved"]) for context in contexts
        )
        summary["interleaved_transition_collision_count"] = sum(
            int(context["transition_collision_count"])
            for context in contexts
            if context["interleaved"]
        )
    return {
        "contexts": contexts,
        "summary": summary,
        "states": child_states,
        "colorings": colorings,
    }


def replay(manifest: dict[str, object], workers: int) -> dict[str, object]:
    k = int(manifest["parameters"]["strong_size"])
    singleton_requested = manifest["singleton_gate"]["contexts"]
    two_root_requested = manifest["two_root_gate"]["contexts"]
    singleton = replay_gate(8, k, singleton_requested, workers, singleton_context)
    two_root = replay_gate(7, k, two_root_requested, workers, two_root_context)
    repo = Path(__file__).resolve().parent.parent
    index_by_bits = {bits: index for index, bits in enumerate(singleton["colorings"])}
    regressions = {}
    for label, pair in regression_pairs(repo, 8).items():
        left = singleton["states"][index_by_bits[pair[0]]]
        right = singleton["states"][index_by_bits[pair[1]]]
        regressions[label] = {
            "left_coloring_hex": f"{pair[0]:x}",
            "right_coloring_hex": f"{pair[1]:x}",
            "equal_quotient": left == right,
        }
    del singleton["states"], singleton["colorings"]
    del two_root["states"], two_root["colorings"]
    return {"singleton_gate": singleton, "two_root_gate": two_root, "regressions": regressions}


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--workers", type=int, default=min(8, os.cpu_count() or 1))
    parser.add_argument(
        "--source-only", action="store_true",
        help="check provenance and recorded stop conditions without exhaustive replay",
    )
    args = parser.parse_args()
    if not 1 <= args.workers <= 8:
        parser.error("workers must lie between 1 and 8")
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported manifest schema")
    repo = Path(__file__).resolve().parent.parent
    source_checks = {
        label: file_sha256(repo / metadata["path"]) == metadata["sha256"]
        for label, metadata in manifest["sources"].items()
    }
    if args.source_only:
        checks = {
            "source_hashes": all(source_checks.values()),
            "recorded_singleton_collision_free": (
                manifest["singleton_gate"]["summary"][
                    "total_transition_collision_count"
                ]
                == 0
            ),
            "recorded_two_root_collision_free": (
                manifest["two_root_gate"]["summary"][
                    "total_transition_collision_count"
                ]
                == 0
            ),
            "recorded_regressions_separated": all(
                not item["equal_quotient"] for item in manifest["regressions"].values()
            ),
        }
        result = {
            "manifest": str(args.manifest),
            "mode": "source-only",
            "source_checks": source_checks,
            "checks": checks,
            "ok": all(checks.values()),
        }
        print(json.dumps(result, indent=2, sort_keys=True))
        if not result["ok"]:
            raise SystemExit(1)
        return
    actual = replay(manifest, args.workers)
    checks = {
        "source_hashes": all(source_checks.values()),
        "singleton_gate": actual["singleton_gate"] == manifest["singleton_gate"],
        "two_root_gate": actual["two_root_gate"] == manifest["two_root_gate"],
        "regressions": actual["regressions"] == manifest["regressions"],
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
