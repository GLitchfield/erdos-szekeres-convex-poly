#!/usr/bin/env python3
"""Produce the bounded rooted span-interface falsification gate.

For a cut ``c``, the recursive state retains the exact raw span footprints on
the two sides.  A crossing port records its cup/cap rank code and its two
distances from the cut, capped at a fixed depth.  Equal ports are counted with
multiplicity clipped at ``k``.  This makes the crossing interface finite in
``k`` and the chosen depth, while deliberately forgetting deeper endpoint
identities.

The producer searches one context in the existing checked raw 8+2 -> 10
census.  The independent checker does not read that machine table: it
reconstructs the recorded witness directly from coloring bits.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import subprocess
from collections import Counter
from pathlib import Path

from enumerate_singleton_residuals import DecomposableColorings
from enumerate_span_rank_footprints import SpanRankFootprint


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


def rooted_signature(record: bytes, n: int, k: int, cut: int, depth: int) -> bytes:
    """Encode the exact-side, capped-distance rooted interface canonically."""
    if record[0]:
        return bytes((1,))
    left = bytearray((0,))
    right = bytearray((0,))
    ports: Counter[tuple[int, int, int]] = Counter()
    for position, (a, b) in enumerate(itertools.combinations(range(n), 2)):
        label = record[1 + position]
        if b < cut:
            left.append(label)
        elif cut <= a:
            right.append(label)
        else:
            ports[(min(depth, cut - a), min(depth, b - cut + 1), label)] += 1
    output = bytearray((0,))
    output.extend(len(left).to_bytes(2, "little"))
    output.extend(left)
    output.extend(len(right).to_bytes(2, "little"))
    output.extend(right)
    output.extend(len(ports).to_bytes(2, "little"))
    for (left_depth, right_depth, label), count in sorted(ports.items()):
        output.extend((left_depth, right_depth, label, min(k, count)))
    return bytes(output)


def class_census(raw_records: tuple[bytes, ...], n: int, k: int) -> list[dict[str, object]]:
    rows = []
    for depth in range(1, 5):
        cuts = []
        for cut in range(1, n):
            fibers: Counter[bytes] = Counter(
                rooted_signature(record, n, k, cut, depth) for record in raw_records
            )
            merged = [size for size in fibers.values() if size > 1]
            cuts.append(
                {
                    "cut": cut,
                    "class_count": len(fibers),
                    "merged_fiber_count": len(merged),
                    "largest_fiber": max(merged, default=1),
                }
            )
        rows.append({"depth": depth, "cuts": cuts})
    return rows


def record_differences(left: bytes, right: bytes, n: int) -> list[dict[str, object]]:
    pairs = tuple(itertools.combinations(range(n), 2))
    return [
        {"pair": list(pairs[index]), "first_code_hex": f"{a:02x}", "second_code_hex": f"{b:02x}"}
        for index, (a, b) in enumerate(zip(left[1:], right[1:]))
        if a != b
    ]


def validate_raw_context(raw_manifest: dict[str, object]) -> dict[str, object]:
    parameters = raw_manifest["parameters"]
    if (
        int(parameters["child_size"]) != 8
        or int(parameters["root_size"]) != 2
        or int(parameters["parent_size"]) != 10
        or int(parameters["strong_size"]) != 6
    ):
        raise ValueError("raw manifest has unexpected parameters")
    for context in raw_manifest["contexts"]:
        if context["root_positions"] == [0, 5] and context["root_role"] == "lower":
            if int(context["transition_collision_count"]) != 0:
                raise ValueError("selected raw context is not a congruence")
            return context
    raise ValueError("selected raw context is missing")


def find_collision(
    colorings: tuple[int, ...],
    child_records: tuple[bytes, ...],
    parent_data: bytes,
    record_size: int,
) -> dict[str, object]:
    representatives: dict[bytes, tuple[int, int]] = {}
    for index, (bits, record) in enumerate(zip(colorings, child_records)):
        representatives.setdefault(record, (bits, index))
    seen: dict[bytes, tuple[bytes, int, bytes, bytes]] = {}
    collision_count = 0
    first = None
    for child_record, (child_bits, index) in representatives.items():
        child_state = rooted_signature(child_record, 8, 6, 4, 3)
        offset = index * record_size
        parent_record = parent_data[offset : offset + record_size]
        parent_state = rooted_signature(parent_record, 10, 6, 5, 3)
        previous = seen.get(child_state)
        if previous is None:
            seen[child_state] = parent_state, child_bits, child_record, parent_record
            continue
        if previous[0] == parent_state:
            continue
        collision_count += 1
        if first is None:
            first_parent_state, first_bits, first_child_record, first_parent_record = previous
            first = {
                "child_coloring_hex": [f"{first_bits:x}", f"{child_bits:x}"],
                "child_raw_footprint_hex": [first_child_record.hex(), child_record.hex()],
                "parent_raw_footprint_hex": [first_parent_record.hex(), parent_record.hex()],
                "child_signature_sha256": hashlib.sha256(child_state).hexdigest(),
                "parent_signature_sha256": [
                    hashlib.sha256(first_parent_state).hexdigest(),
                    hashlib.sha256(parent_state).hexdigest(),
                ],
                "child_raw_differences": record_differences(first_child_record, child_record, 8),
                "parent_raw_differences": record_differences(first_parent_record, parent_record, 10),
            }
    if first is None:
        raise ValueError("candidate unexpectedly passed the selected context")
    return {
        "root_positions": [0, 5],
        "root_role": "lower",
        "designated_root_index": 1,
        "output_orientation": "before",
        "child_cut": 4,
        "parent_cut": 5,
        "depth": 3,
        "raw_representative_count": len(representatives),
        "colliding_signature_fiber_count": collision_count,
        "first_collision": first,
    }


def produce(raw_manifest_path: Path, raw_run_directory: Path) -> dict[str, object]:
    repo = Path(__file__).resolve().parent.parent
    raw_manifest = json.loads(raw_manifest_path.read_text())
    context = validate_raw_context(raw_manifest)
    machine_path = raw_run_directory / "roots-00-05-lower.bin"
    if file_sha256(machine_path) != context["records_sha256"]:
        raise ValueError("raw parent table does not match the checked manifest")
    colorings = DecomposableColorings(8).enumerate()
    footprint = SpanRankFootprint(8, 6)
    child_records = tuple(footprint.encode(bits) for bits in colorings)
    raw_records = tuple(dict.fromkeys(child_records))
    record_size = int(context["record_size"])
    parent_data = machine_path.read_bytes()
    if len(parent_data) != len(colorings) * record_size:
        raise ValueError("raw parent table has the wrong length")
    producer = Path(__file__).resolve()
    checker = repo / "scripts/check_rooted_span_interfaces.py"
    return {
        "schema_version": 1,
        "experiment": "rooted-capped-distance-span-interface",
        "generation_base_revision": git_revision(repo),
        "parameters": {
            "child_size": 8,
            "root_size": 2,
            "parent_size": 10,
            "strong_size": 6,
            "tested_depth": 3,
            "census_depths": [1, 2, 3, 4],
        },
        "contract": {
            "recursive_state": "exact left raw state, exact right raw state, crossing interface",
            "crossing_port": "(min(depth, cut-a), min(depth, b-cut+1), exact rank code)",
            "multiplicity_clip": 6,
            "terminal_state": "one distinguished strong-six symbol",
            "claim_boundary": (
                "Only the crossing interface is finite in k and fixed depth; the exact side states recurse."
            ),
        },
        "review": {
            "git_revision": "b9a94e02c8cba656708afb05433ac227a4980ae0",
            "evidence_packet_sha256": (
                "593e6f8cc88c4c7d7c26175f5d1a864472af90f80e179aa0c83ab783d5cc8aa6"
            ),
            "fable_result_sha256": (
                "b8b72934ab1648102e5191b6ab04ff47f4c98407690763b3e1191822a5040129"
            ),
            "sol_result_sha256": (
                "86587728a787968b5e19386490a0df67c6a43b552aba05d7df7673c246ae23ed"
            ),
            "disposition": "reject on collision or injectivity; then redirect to structural counting",
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
            "raw_manifest": {
                "path": str(raw_manifest_path.relative_to(repo)),
                "sha256": file_sha256(raw_manifest_path),
            },
        },
        "machine_input": {
            "path": str(machine_path.relative_to(repo)),
            "sha256": file_sha256(machine_path),
            "record_count": len(colorings),
            "record_size": record_size,
        },
        "raw_child_footprint_count": len(raw_records),
        "class_census": class_census(raw_records, 8, 6),
        "gate": find_collision(colorings, child_records, parent_data, record_size),
        "stop_condition": {
            "depth_three_transition_collision": True,
            "depth_four_middle_cut_injective": True,
            "candidate_rejected": True,
            "next_route": "structural counting using the raw footprint only as local machinery",
        },
        "scope": (
            "Exact class census for the 46,699 raw k=6 eight-vertex footprint classes at depths "
            "one through four, plus one exact rooted 8+2 -> 10 transition refutation."
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
        "--raw-manifest",
        type=Path,
        default=Path("data/derived/e3-two-root-span-k6-n10.json"),
    )
    parser.add_argument(
        "--raw-run-directory", type=Path, default=Path("runs/e3-two-root-span-k6-n10")
    )
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    write_atomic(
        args.output,
        produce(args.raw_manifest.resolve(), args.raw_run_directory.resolve()),
    )
    print(args.output)


if __name__ == "__main__":
    main()
