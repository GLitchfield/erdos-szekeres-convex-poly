#!/usr/bin/env python3
"""Independently replay a two-vertex-root span-rank congruence manifest.

This checker imports only the prior independent span-footprint checker.  It
imports neither producer, regenerates the recursively decomposable children,
embeds them by a separate routine, and recomputes every parent footprint and
manifest statistic.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import itertools
import json
import os
from collections import Counter
from pathlib import Path

from check_span_rank_footprints import (
    Replay,
    direct_observation,
    footprint_observation,
    parent_crossing,
    span_footprint,
)


_COLORINGS: tuple[int, ...] = ()
_CHILD_STATES: tuple[bytes, ...] = ()
_CHILD_N = 0
_K = 0


def insert_child(bits: int, child_n: int, roots: tuple[int, int]) -> int:
    parent_n = child_n + 2
    parent_positions = {
        triple: index for index, triple in enumerate(itertools.combinations(range(parent_n), 3))
    }
    available = tuple(vertex for vertex in range(parent_n) if vertex not in roots)
    answer = 0
    for index, triple in enumerate(itertools.combinations(range(child_n), 3)):
        if bits & (1 << index):
            image = tuple(available[vertex] for vertex in triple)
            answer |= 1 << parent_positions[image]
    return answer


def is_interleaved(parent_n: int, roots: tuple[int, int]) -> bool:
    return roots not in ((0, 1), (parent_n - 2, parent_n - 1))


def initialize_worker(
    colorings: tuple[int, ...], child_states: tuple[bytes, ...], child_n: int, k: int
) -> None:
    global _COLORINGS, _CHILD_STATES, _CHILD_N, _K
    _COLORINGS = colorings
    _CHILD_STATES = child_states
    _CHILD_N = child_n
    _K = k


def replay_context(context: tuple[tuple[int, int], str]) -> dict[str, object]:
    roots, root_role = context
    parent_n = _CHILD_N + 2
    full = (1 << parent_n) - 1
    root_mask = sum(1 << root for root in roots)
    lower = root_mask if root_role == "lower" else full ^ root_mask
    fixed = parent_crossing(parent_n, lower)
    digest = hashlib.sha256()
    seen = {}
    collisions = 0
    first_collision = None
    readout_mismatches = 0
    parent_states = set()
    for index, child_bits in enumerate(_COLORINGS):
        parent_bits = insert_child(child_bits, _CHILD_N, roots) | fixed
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
        "root_positions": list(roots),
        "root_role": root_role,
        "child_role": "upper" if root_role == "lower" else "lower",
        "lower_mask_hex": f"{lower:x}",
        "interleaved": is_interleaved(parent_n, roots),
        "record_count": len(_COLORINGS),
        "record_size": 1 + len(tuple(itertools.combinations(range(parent_n), 2))),
        "child_state_count": len(seen),
        "parent_state_count": len(parent_states),
        "transition_collision_count": collisions,
        "first_transition_collision": first_collision,
        "observation_readout_mismatch_count": readout_mismatches,
        "records_sha256": digest.hexdigest(),
    }


def summarize(states: tuple[bytes, ...], contexts: list[dict[str, object]]) -> dict[str, object]:
    sizes = Counter(states)
    histogram = Counter(sizes.values())
    interleaved = [context for context in contexts if context["interleaved"]]
    return {
        "coloring_count": len(states),
        "child_footprint_count": len(sizes),
        "nontrivial_child_footprint_count": sum(size > 1 for size in sizes.values()),
        "largest_child_footprint_size": max(sizes.values(), default=0),
        "child_footprint_size_histogram": {
            str(size): count for size, count in sorted(histogram.items())
        },
        "parent_transition_count": len(states) * len(contexts),
        "interleaved_parent_transition_count": len(states) * len(interleaved),
        "total_transition_collision_count": sum(
            int(context["transition_collision_count"]) for context in contexts
        ),
        "interleaved_transition_collision_count": sum(
            int(context["transition_collision_count"]) for context in interleaved
        ),
        "total_observation_readout_mismatch_count": sum(
            int(context["observation_readout_mismatch_count"]) for context in contexts
        ),
    }


def replay(manifest: dict[str, object], workers: int) -> dict[str, object]:
    parameters = manifest["parameters"]
    child_n = int(parameters["child_size"])
    parent_n = child_n + 2
    k = int(parameters["strong_size"])
    colorings = Replay(child_n).normalized_colorings()
    states = tuple(span_footprint(child_n, k, bits) for bits in colorings)
    requested = [
        (roots, role)
        for roots in itertools.combinations(range(parent_n), 2)
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
    contexts.sort(key=lambda item: (item["root_positions"], item["root_role"]))
    return {"contexts": contexts, "summary": summarize(states, contexts)}


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
