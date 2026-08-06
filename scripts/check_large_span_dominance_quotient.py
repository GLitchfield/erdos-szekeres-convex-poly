#!/usr/bin/env python3
"""Independently replay the compact 8+2 -> 10 quotient compatibility gate."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from check_span_dominance_quotients import quotient_record
from check_span_rank_footprints import Replay, parent_crossing, span_footprint
from check_two_root_span_footprints import insert_child


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


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


def replay(raw_manifest: dict[str, object]) -> dict[str, object]:
    colorings = Replay(8).normalized_colorings()
    raw_states = tuple(span_footprint(8, 6, bits) for bits in colorings)
    cache = {}
    states = []
    for record in raw_states:
        state = cache.get(record)
        if state is None:
            state = quotient_record(record, 8, 6)
            cache[record] = state
        states.append(state)
    quotient_states = tuple(states)
    quotient_count, merged = merged_raw_fibers(colorings, raw_states, quotient_states)
    digest = hashlib.sha256()
    collisions = 0
    first_collision = None
    parent_evaluations = 0
    contexts = []
    parent_n = 10
    full = (1 << parent_n) - 1
    for context_index, metadata in enumerate(raw_manifest["contexts"]):
        roots = tuple(int(root) for root in metadata["root_positions"])
        root_role = str(metadata["root_role"])
        root_mask = sum(1 << root for root in roots)
        lower = root_mask if root_role == "lower" else full ^ root_mask
        fixed = parent_crossing(parent_n, lower)
        context_collisions = 0
        for class_id, witnesses in merged:
            parent_states = []
            for _, child_bits in witnesses:
                parent_bits = insert_child(child_bits, 8, roots) | fixed
                raw_parent = span_footprint(parent_n, 6, parent_bits)
                parent_state = quotient_record(raw_parent, parent_n, 6)
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", type=Path)
    parser.add_argument(
        "--source-only", action="store_true",
        help="check provenance and recorded stop conditions without representative replay",
    )
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema_version") != 1:
        parser.error("unsupported manifest schema")
    repo = Path(__file__).resolve().parent.parent
    raw_source = manifest["sources"]["raw_manifest"]
    raw_path = repo / raw_source["path"]
    raw_manifest = json.loads(raw_path.read_text())
    source_checks = {
        label: file_sha256(repo / metadata["path"]) == metadata["sha256"]
        for label, metadata in manifest["sources"].items()
    }
    if args.source_only:
        checks = {
            "source_hashes": all(source_checks.values()),
            "raw_manifest_collision_free": (
                raw_manifest["summary"]["total_transition_collision_count"] == 0
                and raw_manifest["summary"]["total_observation_readout_mismatch_count"] == 0
            ),
            "recorded_quotient_refuted": (
                manifest["gate"]["merged_fiber_transition_collision_count"] > 0
                and manifest["gate"]["first_merged_fiber_transition_collision"] is not None
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
    actual = replay(raw_manifest)
    checks = {
        "source_hashes": all(source_checks.values()),
        "raw_manifest_collision_free": (
            raw_manifest["summary"]["total_transition_collision_count"] == 0
            and raw_manifest["summary"]["total_observation_readout_mismatch_count"] == 0
        ),
        "gate": actual == manifest["gate"],
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
