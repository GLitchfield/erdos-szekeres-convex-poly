#!/usr/bin/env python3
"""Produce the compact 8+2 -> 10 gate for the dominance quotient.

The checked raw-footprint census proves congruence inside each raw child
class.  The quotient merges only a small number of those classes, so this
producer evaluates one representative of every raw class in each nontrivial
quotient fiber.  This reduces the quotient-specific gate from 16,819,920
parents to a compact set of cross-fiber checks.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

from enumerate_singleton_residuals import DecomposableColorings, crossing_bits
from enumerate_span_rank_footprints import SpanRankFootprint
from enumerate_two_root_span_footprints import embed, embedding_table
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


def merged_raw_fibers(
    colorings: tuple[int, ...], raw_states: tuple[bytes, ...], quotient_states: tuple[bytes, ...]
) -> tuple[int, list[tuple[int, list[tuple[bytes, int]]]]]:
    class_ids = {}
    fibers: dict[int, dict[bytes, int]] = {}
    for bits, raw_state, quotient_state in zip(colorings, raw_states, quotient_states):
        class_id = class_ids.setdefault(quotient_state, len(class_ids))
        fibers.setdefault(class_id, {}).setdefault(raw_state, bits)
    merged = [
        (class_id, list(raw_witnesses.items()))
        for class_id, raw_witnesses in fibers.items()
        if len(raw_witnesses) > 1
    ]
    return len(class_ids), merged


def validate_raw_manifest(manifest: dict[str, object]) -> None:
    parameters = manifest["parameters"]
    if (
        int(parameters["child_size"]) != 8
        or int(parameters["root_size"]) != 2
        or int(parameters["parent_size"]) != 10
        or int(parameters["strong_size"]) != 6
    ):
        raise ValueError("raw manifest has unexpected parameters")
    summary = manifest["summary"]
    if int(summary["total_transition_collision_count"]) != 0:
        raise ValueError("raw manifest contains transition collisions")
    if int(summary["total_observation_readout_mismatch_count"]) != 0:
        raise ValueError("raw manifest contains observation mismatches")


def evaluate(
    colorings: tuple[int, ...], raw_states: tuple[bytes, ...],
    quotient_states: tuple[bytes, ...], raw_manifest: dict[str, object],
) -> dict[str, object]:
    quotient_count, merged = merged_raw_fibers(colorings, raw_states, quotient_states)
    parent_n = 10
    k = 6
    parent_footprint = SpanRankFootprint(parent_n, k)
    digest = hashlib.sha256()
    collisions = 0
    first_collision = None
    parent_evaluations = 0
    contexts = []
    full = (1 << parent_n) - 1
    for context_index, metadata in enumerate(raw_manifest["contexts"]):
        roots = tuple(int(root) for root in metadata["root_positions"])
        root_role = str(metadata["root_role"])
        root_mask = sum(1 << root for root in roots)
        lower = root_mask if root_role == "lower" else full ^ root_mask
        fixed = crossing_bits(parent_n, lower)
        table = embedding_table(8, roots)
        context_collisions = 0
        for class_id, witnesses in merged:
            parent_states = []
            for _, child_bits in witnesses:
                parent_bits = embed(child_bits, table) | fixed
                raw_parent = parent_footprint.encode(parent_bits)
                parent_state = encode_span_dominance_quotient(raw_parent, parent_n, k)
                parent_states.append(parent_state)
                parent_evaluations += 1
                digest.update(context_index.to_bytes(2, "little"))
                digest.update(class_id.to_bytes(4, "little"))
                digest.update(len(parent_state).to_bytes(4, "little"))
                digest.update(parent_state)
            if any(state != parent_states[0] for state in parent_states[1:]):
                collisions += 1
                context_collisions += 1
                if first_collision is None:
                    first_collision = {
                        "root_positions": list(roots),
                        "root_role": root_role,
                        "quotient_class_id": class_id,
                        "child_coloring_hex": [f"{bits:x}" for _, bits in witnesses],
                    }
        contexts.append(
            {
                "root_positions": list(roots),
                "root_role": root_role,
                "interleaved": metadata["interleaved"],
                "merged_fiber_collision_count": context_collisions,
            }
        )
    first_fiber = None
    if merged:
        class_id, witnesses = min(merged)
        first_fiber = {
            "class_id": class_id,
            "raw_footprint_count": len(witnesses),
            "coloring_hex": [f"{bits:x}" for _, bits in witnesses],
        }
    return {
        "raw_parent_transition_count": raw_manifest["summary"]["parent_transition_count"],
        "raw_interleaved_parent_transition_count": raw_manifest["summary"][
            "interleaved_parent_transition_count"
        ],
        "raw_child_footprint_count": len(set(raw_states)),
        "quotient_state_count": quotient_count,
        "merged_quotient_fiber_count": len(merged),
        "merged_raw_footprint_count": sum(len(witnesses) for _, witnesses in merged),
        "largest_merged_raw_fiber": max((len(witnesses) for _, witnesses in merged), default=0),
        "first_merged_raw_fiber": first_fiber,
        "context_count": len(contexts),
        "interleaved_context_count": sum(bool(context["interleaved"]) for context in contexts),
        "parent_representative_evaluation_count": parent_evaluations,
        "merged_fiber_transition_collision_count": collisions,
        "first_merged_fiber_transition_collision": first_collision,
        "representative_parent_records_sha256": digest.hexdigest(),
        "contexts": contexts,
    }


def produce(raw_manifest_path: Path) -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    raw_manifest = json.loads(raw_manifest_path.read_text())
    validate_raw_manifest(raw_manifest)
    colorings = DecomposableColorings(8).enumerate()
    footprint = SpanRankFootprint(8, 6)
    raw_states = tuple(footprint.encode(bits) for bits in colorings)
    cache = {}
    states = []
    for record in raw_states:
        state = cache.get(record)
        if state is None:
            state = encode_span_dominance_quotient(record, 8, 6)
            cache[record] = state
        states.append(state)
    quotient_states = tuple(states)
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_large_span_dominance_quotient.py"
    quotient = repo / "scripts/span_dominance_quotient.py"
    independent_quotient = repo / "scripts/check_span_dominance_quotients.py"
    return {
        "schema_version": 1,
        "experiment": "large-span-dominance-incidence-quotient",
        "generation_base_revision": git_revision(repo),
        "parameters": {
            "child_size": 8,
            "root_size": 2,
            "parent_size": 10,
            "strong_size": 6,
        },
        "sources": {
            "producer": {"path": str(producer.relative_to(repo)), "sha256": file_sha256(producer)},
            "checker": {"path": str(checker.relative_to(repo)), "sha256": file_sha256(checker)},
            "quotient": {"path": str(quotient.relative_to(repo)), "sha256": file_sha256(quotient)},
            "independent_quotient": {
                "path": str(independent_quotient.relative_to(repo)),
                "sha256": file_sha256(independent_quotient),
            },
            "raw_manifest": {
                "path": str(raw_manifest_path.relative_to(repo)),
                "sha256": file_sha256(raw_manifest_path),
            },
        },
        "gate": evaluate(colorings, raw_states, quotient_states, raw_manifest),
        "scope": (
            "Exact quotient compatibility across every nontrivial raw-footprint fiber, "
            "under every two-root placement and role, conditional on the independently "
            "replayed raw 8+2 -> 10 footprint congruence census."
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
        "--raw-manifest", type=Path,
        default=Path("data/derived/e3-two-root-span-k6-n10.json"),
    )
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parent.parent
    raw_manifest_path = (repo / args.raw_manifest).resolve()
    write_atomic(args.output, produce(raw_manifest_path))
    print(args.output)


if __name__ == "__main__":
    main()
