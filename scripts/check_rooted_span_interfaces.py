#!/usr/bin/env python3
"""Independently check the rooted capped-distance interface refutation."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

from check_span_rank_footprints import Replay, parent_crossing, span_footprint
from check_two_root_span_footprints import insert_child


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def independent_signature(record: bytes, n: int, k: int, cut: int, depth: int) -> bytes:
    if record[0] == 1:
        return b"\x01"
    left_codes = []
    right_codes = []
    counts: dict[tuple[int, int, int], int] = {}
    for position, pair in enumerate(itertools.combinations(range(n), 2)):
        a, b = pair
        code = record[position + 1]
        if b < cut:
            left_codes.append(code)
        elif a >= cut:
            right_codes.append(code)
        else:
            key = (min(cut - a, depth), min(b - cut + 1, depth), code)
            counts[key] = counts.get(key, 0) + 1
    encoded = bytearray(b"\x00")
    left = bytes((0, *left_codes))
    right = bytes((0, *right_codes))
    encoded.extend(len(left).to_bytes(2, "little"))
    encoded.extend(left)
    encoded.extend(len(right).to_bytes(2, "little"))
    encoded.extend(right)
    encoded.extend(len(counts).to_bytes(2, "little"))
    for (left_depth, right_depth, code), count in sorted(counts.items()):
        encoded.extend((left_depth, right_depth, code, min(count, k)))
    return bytes(encoded)


def census(records: tuple[bytes, ...], n: int, k: int) -> list[dict[str, object]]:
    result = []
    for depth in range(1, 5):
        per_cut = []
        for cut in range(1, n):
            sizes = Counter(independent_signature(record, n, k, cut, depth) for record in records)
            nontrivial = [size for size in sizes.values() if size >= 2]
            per_cut.append(
                {
                    "cut": cut,
                    "class_count": len(sizes),
                    "merged_fiber_count": len(nontrivial),
                    "largest_fiber": max(nontrivial, default=1),
                }
            )
        result.append({"depth": depth, "cuts": per_cut})
    return result


def differing_pairs(first: bytes, second: bytes, n: int) -> list[dict[str, object]]:
    pairs = list(itertools.combinations(range(n), 2))
    output = []
    for index in range(len(pairs)):
        left = first[index + 1]
        right = second[index + 1]
        if left != right:
            output.append(
                {
                    "pair": list(pairs[index]),
                    "first_code_hex": format(left, "02x"),
                    "second_code_hex": format(right, "02x"),
                }
            )
    return output


def replay_witness(manifest: dict[str, object]) -> dict[str, object]:
    gate = manifest["gate"]
    witness = gate["first_collision"]
    child_bits = tuple(int(value, 16) for value in witness["child_coloring_hex"])
    child_records = tuple(span_footprint(8, 6, bits) for bits in child_bits)
    roots = tuple(int(value) for value in gate["root_positions"])
    lower = sum(1 << root for root in roots)
    fixed = parent_crossing(10, lower)
    parent_bits = tuple(insert_child(bits, 8, roots) | fixed for bits in child_bits)
    parent_records = tuple(span_footprint(10, 6, bits) for bits in parent_bits)
    child_states = tuple(independent_signature(record, 8, 6, 4, 3) for record in child_records)
    parent_states = tuple(independent_signature(record, 10, 6, 5, 3) for record in parent_records)
    return {
        "child_coloring_hex": [format(bits, "x") for bits in child_bits],
        "child_raw_footprint_hex": [record.hex() for record in child_records],
        "parent_raw_footprint_hex": [record.hex() for record in parent_records],
        "child_signature_sha256": hashlib.sha256(child_states[0]).hexdigest(),
        "parent_signature_sha256": [hashlib.sha256(state).hexdigest() for state in parent_states],
        "child_raw_differences": differing_pairs(*child_records, 8),
        "parent_raw_differences": differing_pairs(*parent_records, 10),
        "child_signatures_equal": child_states[0] == child_states[1],
        "parent_signatures_different": parent_states[0] != parent_states[1],
        "parent_terminal": [bool(record[0]) for record in parent_records],
    }


def source_checks(manifest: dict[str, object], repo: Path) -> dict[str, bool]:
    return {
        label: file_sha256(repo / metadata["path"]) == metadata["sha256"]
        for label, metadata in manifest["sources"].items()
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported manifest schema")
    repo = Path(__file__).resolve().parent.parent
    sources = source_checks(manifest, repo)
    depth_three = next(row for row in manifest["class_census"] if row["depth"] == 3)
    depth_four = next(row for row in manifest["class_census"] if row["depth"] == 4)
    depth_four_middle = next(row for row in depth_four["cuts"] if row["cut"] == 4)
    recorded_checks = {
        "source_hashes": all(sources.values()),
        "depth_three_noninjective_at_every_cut": all(
            row["class_count"] < manifest["raw_child_footprint_count"]
            for row in depth_three["cuts"]
        ),
        "depth_four_middle_cut_injective": (
            depth_four_middle["class_count"] == manifest["raw_child_footprint_count"]
        ),
        "candidate_recorded_refuted": (
            manifest["stop_condition"]["candidate_rejected"]
            and manifest["gate"]["first_collision"] is not None
        ),
    }
    if args.source_only:
        result = {
            "manifest": str(args.manifest),
            "mode": "source-only",
            "source_checks": sources,
            "checks": recorded_checks,
            "ok": all(recorded_checks.values()),
        }
    else:
        colorings = Replay(8).normalized_colorings()
        raw_records = tuple(
            dict.fromkeys(span_footprint(8, 6, bits) for bits in colorings)
        )
        witness = replay_witness(manifest)
        expected_witness = dict(manifest["gate"]["first_collision"])
        actual_witness = {key: witness[key] for key in expected_witness}
        exhaustive_checks = {
            **recorded_checks,
            "raw_child_footprint_count": len(raw_records) == manifest["raw_child_footprint_count"],
            "class_census": census(raw_records, 8, 6) == manifest["class_census"],
            "witness_payload": actual_witness == expected_witness,
            "child_signatures_equal": witness["child_signatures_equal"],
            "parent_signatures_different": witness["parent_signatures_different"],
            "parents_open": not any(witness["parent_terminal"]),
        }
        result = {
            "manifest": str(args.manifest),
            "mode": "exhaustive",
            "source_checks": sources,
            "checks": exhaustive_checks,
            "witness": witness,
            "ok": all(exhaustive_checks.values()),
        }
    print(json.dumps(result, indent=2, sort_keys=True))
    if not result["ok"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
