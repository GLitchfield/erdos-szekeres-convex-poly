#!/usr/bin/env python3
"""Produce the exact k=6 singleton transition gate for span-rank footprints.

The footprint of an open coloring stores, for every ordered endpoint pair,
the largest cup and cap having exactly those endpoints, clipped below ``k``.
A coloring containing a strong ``k``-set is one terminal state.  This retains
the two-gap endpoint incidence lost by the all-gap maxima while forgetting the
internal vertices of every witness chain.

Large parent-state tables are machine-local under ``runs/``.  The independent
checker imports neither this module nor the residual-oracle producer.
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
from dataclasses import dataclass
from pathlib import Path

from enumerate_singleton_residuals import (
    DecomposableColorings,
    Observation,
    crossing_bits,
    embed,
    embedding_tables,
    load_regressions,
)


@dataclass(frozen=True)
class Chain:
    size: int
    first: int
    last: int
    required: int


class SpanRankFootprint:
    def __init__(self, n: int, k: int):
        self.n = n
        self.k = k
        self.triples = tuple(itertools.combinations(range(n), 3))
        positions = {triple: index for index, triple in enumerate(self.triples)}
        self.pairs = tuple(itertools.combinations(range(n), 2))
        self.pair_positions = {pair: index for index, pair in enumerate(self.pairs)}
        self.chains = []
        self.strong_equalities = []
        for size in range(2, min(n, k - 1) + 1):
            for vertices in itertools.combinations(range(n), size):
                required = sum(
                    1 << positions[triple]
                    for triple in itertools.combinations(vertices, 3)
                )
                self.chains.append(
                    Chain(size, vertices[0], vertices[-1], required)
                )
        if k <= n:
            for vertices in itertools.combinations(range(n), k):
                equalities = []
                for a, b, c, d in itertools.combinations(vertices, 4):
                    equalities.append(
                        (1 << positions[(a, b, c)]) | (1 << positions[(a, b, d)])
                    )
                    equalities.append(
                        (1 << positions[(a, c, d)]) | (1 << positions[(b, c, d)])
                    )
                self.strong_equalities.append(tuple(equalities))
        self.record_size = 1 + len(self.pairs)
        self.closed_record = bytes((1,)) + bytes(len(self.pairs))

    @staticmethod
    def equality(bits: int, mask: int) -> bool:
        selected = bits & mask
        return selected == 0 or selected == mask

    def closed(self, bits: int) -> bool:
        return any(
            all(self.equality(bits, mask) for mask in equalities)
            for equalities in self.strong_equalities
        )

    def encode(self, bits: int) -> bytes:
        if self.closed(bits):
            return self.closed_record
        cup = [0] * len(self.pairs)
        cap = [0] * len(self.pairs)
        for chain in self.chains:
            index = self.pair_positions[(chain.first, chain.last)]
            if bits & chain.required == chain.required:
                cup[index] = max(cup[index], chain.size)
            if bits & chain.required == 0:
                cap[index] = max(cap[index], chain.size)
        return bytes((0,)) + bytes(a | (b << 4) for a, b in zip(cup, cap))

    def observation(self, record: bytes) -> bytes:
        size = 1 + 4 * (self.n + 1)
        if record[0]:
            return bytes((1,)) + bytes(size - 1)
        values = [[0] * 6 for _ in range(self.n + 1)]
        for vertex in range(self.n):
            for gap in range(self.n + 1):
                relation = 0 if gap <= vertex else 1
                values[gap][relation] = max(values[gap][relation], 1)
                values[gap][3 + relation] = max(values[gap][3 + relation], 1)
        for index, (first, last) in enumerate(self.pairs):
            code = record[1 + index]
            cup = code & 15
            cap = code >> 4
            for gap in range(self.n + 1):
                relation = 0 if gap <= first else 1 if gap > last else 2
                values[gap][relation] = max(values[gap][relation], cup)
                values[gap][3 + relation] = max(values[gap][3 + relation], cap)
        output = bytearray((0,))
        for row in values:
            word = sum(value << (3 * coordinate) for coordinate, value in enumerate(row))
            output.extend(word.to_bytes(4, "little"))
        return bytes(output)


_COLORINGS: tuple[int, ...] = ()
_CHILD_STATES: tuple[bytes, ...] = ()
_CHILD_N = 0
_K = 0
_DIRECTORY = Path()


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


def context_name(root: int, role: str) -> str:
    return f"root-{root:02d}-child-{role}"


def produce_context(context: tuple[int, str]) -> dict[str, object]:
    root, role = context
    parent_n = _CHILD_N + 1
    full = (1 << parent_n) - 1
    singleton = 1 << root
    lower = singleton if role == "upper" else full ^ singleton
    fixed = crossing_bits(parent_n, lower)
    tables = embedding_tables(_CHILD_N, root)
    footprint = SpanRankFootprint(parent_n, _K)
    observation = Observation(parent_n, _K)
    path = _DIRECTORY / f"{context_name(root, role)}.bin"
    temporary = path.with_suffix(".bin.tmp")
    state_digest = hashlib.sha256()
    seen = {}
    collisions = 0
    first_collision = None
    readout_mismatches = 0
    parent_states = set()
    with temporary.open("wb") as stream:
        for index, child_bits in enumerate(_COLORINGS):
            parent_bits = embed(child_bits, tables) | fixed
            parent_state = footprint.encode(parent_bits)
            parent_states.add(parent_state)
            stream.write(parent_state)
            state_digest.update(parent_state)
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
        "root": root,
        "child_role": role,
        "lower_mask_hex": f"{lower:x}",
        "record_count": len(_COLORINGS),
        "record_size": footprint.record_size,
        "child_state_count": len(seen),
        "parent_state_count": len(parent_states),
        "transition_collision_count": collisions,
        "first_transition_collision": first_collision,
        "observation_readout_mismatch_count": readout_mismatches,
        "records_sha256": state_digest.hexdigest(),
        "machine_file": str(path),
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


def summarize(repo: Path, colorings: tuple[int, ...], states: tuple[bytes, ...],
              child_n: int, contexts: list[dict[str, object]]) -> dict[str, object]:
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
    regressions = {}
    index_by_bits = {bits: index for index, bits in enumerate(colorings)}
    for label, pair in load_regressions(repo, child_n).items():
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


def produce(child_n: int, k: int, workers: int, directory: Path) -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    directory.mkdir(parents=True, exist_ok=True)
    colorings = DecomposableColorings(child_n).enumerate()
    child_footprint = SpanRankFootprint(child_n, k)
    child_observation = Observation(child_n, k)
    states = tuple(child_footprint.encode(bits) for bits in colorings)
    child_readout_mismatches = sum(
        child_footprint.observation(state) != child_observation.encode(bits)
        for bits, state in zip(colorings, states)
    )
    contexts = [
        (root, role)
        for root in range(child_n + 1)
        for role in ("lower", "upper")
    ]
    initialize_worker(colorings, states, child_n, k, str(directory))
    if workers == 1:
        metadata = [produce_context(context) for context in contexts]
    else:
        with concurrent.futures.ProcessPoolExecutor(
            max_workers=workers,
            initializer=initialize_worker,
            initargs=(colorings, states, child_n, k, str(directory)),
        ) as pool:
            metadata = list(pool.map(produce_context, contexts))
    metadata.sort(key=lambda item: (int(item["root"]), str(item["child_role"])))
    summary = summarize(repo, colorings, states, child_n, metadata)
    summary["child_observation_readout_mismatch_count"] = child_readout_mismatches
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_span_rank_footprints.py"
    dependency = repo / "scripts/enumerate_singleton_residuals.py"
    public_contexts = [
        {key: value for key, value in item.items() if key != "machine_file"}
        for item in metadata
    ]
    return {
        "schema_version": 1,
        "experiment": "span-rank-singleton-congruence",
        "generation_base_revision": git_revision(repo),
        "parameters": {
            "child_size": child_n,
            "parent_size": child_n + 1,
            "strong_size": k,
            "context_count": len(contexts),
            "open_state": (
                "lexicographic endpoint pairs; one byte per pair; low nibble "
                "is maximum cup size and high nibble is maximum cap size"
            ),
            "closed_state": "one terminal symbol",
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
                "path": str(dependency.relative_to(repo)),
                "sha256": file_sha256(dependency),
            },
        },
        "contexts": public_contexts,
        "summary": summary,
        "scope": (
            f"Exact for all decomposable {child_n}-vertex colorings and all "
            f"{2 * (child_n + 1)} singleton root contexts at k={k}."
        ),
    }


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--child-size", type=int, default=8)
    parser.add_argument("--strong-size", type=int, default=6)
    parser.add_argument("--workers", type=int, default=min(8, os.cpu_count() or 1))
    parser.add_argument("--run-directory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not 3 <= args.child_size <= 8:
        parser.error("child-size must lie between 3 and 8")
    if not 4 <= args.strong_size <= args.child_size + 1:
        parser.error("strong-size must lie between 4 and child-size + 1")
    if not 1 <= args.workers <= 8:
        parser.error("workers must lie between 1 and 8")
    write_atomic(
        args.output,
        produce(
            args.child_size,
            args.strong_size,
            args.workers,
            args.run_directory.resolve(),
        ),
    )
    print(args.output)


if __name__ == "__main__":
    main()
