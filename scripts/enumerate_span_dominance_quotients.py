#!/usr/bin/env python3
"""Produce the bounded gates for the span-dominance incidence quotient.

The producer consumes the already checked raw singleton and two-root machine
tables.  It verifies every raw table digest before use, recomputes the child
quotients, and checks quotient congruence.  The independent checker imports
neither this module nor the quotient encoder and reconstructs every raw parent
directly from its coloring.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import subprocess

from enumerate_singleton_residuals import DecomposableColorings, load_regressions
from enumerate_span_rank_footprints import SpanRankFootprint
from span_dominance_quotient import encode_span_dominance_quotient


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


def update_variable_digest(digest: hashlib._Hash, record: bytes) -> None:
    digest.update(len(record).to_bytes(4, "little"))
    digest.update(record)


def read_fixed_records(path: Path, record_size: int, record_count: int):
    expected_size = record_size * record_count
    if path.stat().st_size != expected_size:
        raise ValueError(f"unexpected byte length for {path}")
    with path.open("rb") as stream:
        for _ in range(record_count):
            record = stream.read(record_size)
            if len(record) != record_size:
                raise ValueError(f"truncated record in {path}")
            yield record
        if stream.read(1):
            raise ValueError(f"trailing bytes in {path}")


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


def check_context(
    metadata: dict[str, object], path: Path, child_states: tuple[bytes, ...],
    parent_n: int, k: int, parent_cache: dict[bytes, bytes],
) -> dict[str, object]:
    record_size = int(metadata["record_size"])
    record_count = int(metadata["record_count"])
    raw_digest = file_sha256(path)
    if raw_digest != metadata["records_sha256"]:
        raise ValueError(f"raw table digest mismatch for {path}")
    seen = {}
    collisions = 0
    first_collision = None
    parent_states = set()
    quotient_digest = hashlib.sha256()
    for index, raw_parent in enumerate(read_fixed_records(path, record_size, record_count)):
        parent_state = parent_cache.get(raw_parent)
        if parent_state is None:
            parent_state = encode_span_dominance_quotient(raw_parent, parent_n, k)
            parent_cache[raw_parent] = parent_state
        parent_states.add(parent_state)
        update_variable_digest(quotient_digest, parent_state)
        child_state = child_states[index]
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
        "child_quotient_state_count": len(seen),
        "parent_quotient_state_count": len(parent_states),
        "transition_collision_count": collisions,
        "first_transition_collision": first_collision,
        "quotient_records_sha256": quotient_digest.hexdigest(),
    }


def singleton_file_name(metadata: dict[str, object]) -> str:
    return f"root-{int(metadata['root']):02d}-child-{metadata['child_role']}.bin"


def two_root_file_name(metadata: dict[str, object]) -> str:
    roots = metadata["root_positions"]
    return f"roots-{int(roots[0]):02d}-{int(roots[1]):02d}-{metadata['root_role']}.bin"


def produce_gate(
    manifest: dict[str, object], run_directory: Path, child_n: int, k: int,
    file_name,
) -> dict[str, object]:
    colorings = DecomposableColorings(child_n).enumerate()
    footprint = SpanRankFootprint(child_n, k)
    raw_states = tuple(footprint.encode(bits) for bits in colorings)
    cache = {}
    states = []
    for record in raw_states:
        state = cache.get(record)
        if state is None:
            state = encode_span_dominance_quotient(record, child_n, k)
            cache[record] = state
        states.append(state)
    child_states = tuple(states)
    parent_cache: dict[bytes, bytes] = {}
    contexts = []
    for metadata in manifest["contexts"]:
        result = check_context(
            metadata,
            run_directory / file_name(metadata),
            child_states,
            child_n + (int(manifest["parameters"].get("root_size", 1))),
            k,
            parent_cache,
        )
        context_keys = (
            ("root", "child_role")
            if "root" in metadata
            else ("root_positions", "root_role", "child_role", "interleaved")
        )
        contexts.append({**{key: metadata[key] for key in context_keys}, **result})
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
    return {"contexts": contexts, "summary": summary, "states": child_states, "colorings": colorings}


def produce(
    singleton_manifest_path: Path, singleton_run_directory: Path,
    two_root_manifest_path: Path, two_root_run_directory: Path,
) -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    singleton_manifest = json.loads(singleton_manifest_path.read_text())
    two_root_manifest = json.loads(two_root_manifest_path.read_text())
    singleton = produce_gate(singleton_manifest, singleton_run_directory, 8, 6, singleton_file_name)
    two_root = produce_gate(two_root_manifest, two_root_run_directory, 7, 6, two_root_file_name)
    index_by_bits = {bits: index for index, bits in enumerate(singleton["colorings"])}
    regressions = {}
    for label, pair in load_regressions(repo, 8).items():
        left = singleton["states"][index_by_bits[pair[0]]]
        right = singleton["states"][index_by_bits[pair[1]]]
        regressions[label] = {
            "left_coloring_hex": f"{pair[0]:x}",
            "right_coloring_hex": f"{pair[1]:x}",
            "equal_quotient": left == right,
        }
    del singleton["states"], singleton["colorings"]
    del two_root["states"], two_root["colorings"]
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_span_dominance_quotients.py"
    quotient = repo / "scripts/span_dominance_quotient.py"
    return {
        "schema_version": 1,
        "experiment": "span-dominance-incidence-quotient",
        "generation_base_revision": git_revision(repo),
        "parameters": {
            "strong_size": 6,
            "singleton_child_size": 8,
            "two_root_child_size": 7,
            "rank_histogram_clip": 6,
            "endpoint_multiplicity_clip": 6,
            "coarse_incidence_threshold": 3,
        },
        "sources": {
            "producer": {"path": str(producer.relative_to(repo)), "sha256": file_sha256(producer)},
            "checker": {"path": str(checker.relative_to(repo)), "sha256": file_sha256(checker)},
            "quotient": {"path": str(quotient.relative_to(repo)), "sha256": file_sha256(quotient)},
            "singleton_manifest": {
                "path": str(singleton_manifest_path.relative_to(repo)),
                "sha256": file_sha256(singleton_manifest_path),
            },
            "two_root_manifest": {
                "path": str(two_root_manifest_path.relative_to(repo)),
                "sha256": file_sha256(two_root_manifest_path),
            },
        },
        "singleton_gate": singleton,
        "two_root_gate": two_root,
        "regressions": regressions,
        "scope": (
            "Exact for every decomposable eight-vertex child and all singleton contexts, "
            "and every decomposable seven-vertex child and all two-root contexts, at k=6."
        ),
    }


def write_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--singleton-manifest", type=Path,
        default=Path("data/derived/e3-span-rank-footprint-k6-n9.json"),
    )
    parser.add_argument("--singleton-run-directory", type=Path, required=True)
    parser.add_argument(
        "--two-root-manifest", type=Path,
        default=Path("data/derived/e3-two-root-span-k6-n9.json"),
    )
    parser.add_argument("--two-root-run-directory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    write_atomic(
        args.output,
        produce(
            (repo / args.singleton_manifest).resolve(),
            args.singleton_run_directory.resolve(),
            (repo / args.two_root_manifest).resolve(),
            args.two_root_run_directory.resolve(),
        ),
    )
    print(args.output)


if __name__ == "__main__":
    main()
