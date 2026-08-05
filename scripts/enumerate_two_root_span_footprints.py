#!/usr/bin/env python3
"""Produce the exact two-vertex-root congruence gate for span-rank footprints.

The root child has two vertices and hence a unique internal coloring.  For
every placement of those vertices and both lower/upper root roles, the
producer adjoins the root to every decomposable child coloring and checks
whether equal child span footprints always yield equal parent footprints.
Large parent tables are written only below the requested ignored run path.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import itertools
import json
import os
import subprocess
from collections import Counter
from pathlib import Path

from enumerate_singleton_residuals import DecomposableColorings, Observation, crossing_bits
from enumerate_span_rank_footprints import SpanRankFootprint


_COLORINGS: tuple[int, ...] = ()
_CHILD_STATES: tuple[bytes, ...] = ()
_CHILD_N = 0
_K = 0
_DIRECTORY = Path()


def embedding_table(child_n: int, roots: tuple[int, int]) -> tuple[int, ...]:
    parent_n = child_n + 2
    child_positions = {
        triple: index for index, triple in enumerate(itertools.combinations(range(child_n), 3))
    }
    parent_positions = {
        triple: index for index, triple in enumerate(itertools.combinations(range(parent_n), 3))
    }
    available = tuple(vertex for vertex in range(parent_n) if vertex not in roots)
    table = [0] * len(child_positions)
    for triple, child_index in child_positions.items():
        image = tuple(available[vertex] for vertex in triple)
        table[child_index] = 1 << parent_positions[image]
    return tuple(table)


def embed(bits: int, table: tuple[int, ...]) -> int:
    answer = 0
    for index, image in enumerate(table):
        if bits & (1 << index):
            answer |= image
    return answer


def is_interleaved(parent_n: int, roots: tuple[int, int]) -> bool:
    return roots not in ((0, 1), (parent_n - 2, parent_n - 1))


def context_name(roots: tuple[int, int], root_role: str) -> str:
    return f"roots-{roots[0]:02d}-{roots[1]:02d}-{root_role}"


def initialize_worker(
    colorings: tuple[int, ...], child_states: tuple[bytes, ...], child_n: int,
    k: int, directory: str,
) -> None:
    global _COLORINGS, _CHILD_STATES, _CHILD_N, _K, _DIRECTORY
    _COLORINGS = colorings
    _CHILD_STATES = child_states
    _CHILD_N = child_n
    _K = k
    _DIRECTORY = Path(directory)


def produce_context(context: tuple[tuple[int, int], str]) -> dict[str, object]:
    roots, root_role = context
    parent_n = _CHILD_N + 2
    full = (1 << parent_n) - 1
    root_mask = sum(1 << root for root in roots)
    lower = root_mask if root_role == "lower" else full ^ root_mask
    fixed = crossing_bits(parent_n, lower)
    table = embedding_table(_CHILD_N, roots)
    footprint = SpanRankFootprint(parent_n, _K)
    observation = Observation(parent_n, _K)
    path = _DIRECTORY / f"{context_name(roots, root_role)}.bin"
    temporary = path.with_suffix(".bin.tmp")
    digest = hashlib.sha256()
    seen = {}
    collisions = 0
    first_collision = None
    readout_mismatches = 0
    parent_states = set()
    with temporary.open("wb") as stream:
        for index, child_bits in enumerate(_COLORINGS):
            parent_bits = embed(child_bits, table) | fixed
            parent_state = footprint.encode(parent_bits)
            parent_states.add(parent_state)
            stream.write(parent_state)
            digest.update(parent_state)
            if footprint.observation(parent_state) != observation.encode(parent_bits):
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
    os.replace(temporary, path)
    return {
        "root_positions": list(roots),
        "root_role": root_role,
        "child_role": "upper" if root_role == "lower" else "lower",
        "lower_mask_hex": f"{lower:x}",
        "interleaved": is_interleaved(parent_n, roots),
        "record_count": len(_COLORINGS),
        "record_size": footprint.record_size,
        "child_state_count": len(seen),
        "parent_state_count": len(parent_states),
        "transition_collision_count": collisions,
        "first_transition_collision": first_collision,
        "observation_readout_mismatch_count": readout_mismatches,
        "records_sha256": digest.hexdigest(),
        "machine_file": str(path),
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


def file_sha256(path: Path) -> str:
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


def produce(child_n: int, k: int, workers: int, directory: Path) -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    directory.mkdir(parents=True, exist_ok=True)
    colorings = DecomposableColorings(child_n).enumerate()
    child_footprint = SpanRankFootprint(child_n, k)
    states = tuple(child_footprint.encode(bits) for bits in colorings)
    parent_n = child_n + 2
    requested = [
        (roots, role)
        for roots in itertools.combinations(range(parent_n), 2)
        for role in ("lower", "upper")
    ]
    initialize_worker(colorings, states, child_n, k, str(directory))
    if workers == 1:
        contexts = [produce_context(context) for context in requested]
    else:
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=workers,
            initializer=initialize_worker,
            initargs=(colorings, states, child_n, k, str(directory)),
        ) as pool:
            contexts = list(pool.map(produce_context, requested))
    contexts.sort(key=lambda item: (item["root_positions"], item["root_role"]))
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_two_root_span_footprints.py"
    producer_dependency = repo / "scripts/enumerate_span_rank_footprints.py"
    checker_dependency = repo / "scripts/check_span_rank_footprints.py"
    return {
        "schema_version": 1,
        "experiment": "two-root-span-rank-congruence",
        "generation_base_revision": git_revision(repo),
        "parameters": {
            "child_size": child_n,
            "root_size": 2,
            "parent_size": parent_n,
            "strong_size": k,
            "context_count": len(contexts),
            "interleaved_context_count": sum(context["interleaved"] for context in contexts),
        },
        "sources": {
            "producer": {
                "path": str(producer.relative_to(repo)),
                "sha256": file_sha256(producer),
            },
            "checker": {
                "path": str(checker.relative_to(repo)),
                "sha256": file_sha256(checker),
            },
            "producer_dependency": {
                "path": str(producer_dependency.relative_to(repo)),
                "sha256": file_sha256(producer_dependency),
            },
            "checker_dependency": {
                "path": str(checker_dependency.relative_to(repo)),
                "sha256": file_sha256(checker_dependency),
            },
        },
        "contexts": [
            {key: value for key, value in context.items() if key != "machine_file"}
            for context in contexts
        ],
        "summary": summarize(states, contexts),
        "scope": (
            f"Exact for every decomposable {child_n}-vertex coloring, every placement "
            f"of a two-vertex root, and both root roles at k={k}."
        ),
    }


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--child-size", type=int, default=7)
    parser.add_argument("--strong-size", type=int, default=6)
    parser.add_argument("--workers", type=int, default=min(8, os.cpu_count() or 1))
    parser.add_argument("--run-directory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 3 <= args.child_size <= 8:
        parser.error("child-size must lie between 3 and 8")
    if not 4 <= args.strong_size <= min(9, args.child_size + 2):
        parser.error("strong-size must lie between 4 and min(9, child-size + 2)")
    if not 1 <= args.workers <= 8:
        parser.error("workers must lie between 1 and 8")
    write_atomic(
        args.output,
        produce(args.child_size, args.strong_size, args.workers, args.run_directory.resolve()),
    )
    print(args.output)


if __name__ == "__main__":
    main()
