#!/usr/bin/env python3
"""Independently check cap-failure charge matching certificates."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path


Signature = tuple[int, int]
Slot = tuple[Signature, int]

SIGNATURES: tuple[Signature, ...] = tuple(
    (gap, index)
    for gap in range(5)
    for index in range(3)
    if index <= gap <= index + 2
)
SLOTS: set[Slot] = {
    (signature, copy) for signature in SIGNATURES for copy in range(2)
}


def realized(
    cap: tuple[int, ...], vertex: int,
    left_turns: set[tuple[int, int, int]],
) -> set[Signature]:
    five = tuple(sorted((*cap, vertex)))
    gap = five.index(vertex)
    return {
        (gap, index) for index in range(3)
        if index <= gap <= index + 2
        and five[index:index + 3] in left_turns
    }


def verify(model_path: Path, certificate_path: Path) -> None:
    model_bytes = model_path.read_bytes()
    model = json.loads(model_bytes)
    certificate = json.loads(certificate_path.read_text())
    if certificate.get("schema_version") != 1:
        raise ValueError("certificate schema_version must be one")
    if certificate.get("model_sha256") != hashlib.sha256(model_bytes).hexdigest():
        raise ValueError("model SHA-256 mismatch")
    validation = model.get("validation")
    if not isinstance(validation, dict) or validation.get("valid") is not True:
        raise ValueError("model validation is absent or false")
    n, cut = model.get("n"), model.get("cut")
    if certificate.get("n") != n or certificate.get("cut") != cut:
        raise ValueError("certificate parameters do not match model")
    left_turns = {tuple(triple) for triple in model.get("left_triples", [])}
    expected_caps = {
        cap for cap in itertools.combinations(range(n), 4)
        if min(cap) < cut <= max(cap)
        and all(triple not in left_turns
                for triple in itertools.combinations(cap, 3))
    }

    seen_caps = set()
    histogram: Counter[int] = Counter()
    for record in certificate.get("records", []):
        cap = tuple(record.get("cap", []))
        if cap not in expected_caps or cap in seen_caps:
            raise ValueError(f"unexpected or duplicate cap {cap}")
        seen_caps.add(cap)
        outside = set(range(n)) - set(cap)
        matching = record.get("matching", [])
        matched_vertices = set()
        used_slots = set()
        for item in matching:
            if not isinstance(item, list) or len(item) != 4:
                raise ValueError(f"malformed matching item for cap {cap}")
            vertex, gap, index, copy = item
            signature, slot = (gap, index), ((gap, index), copy)
            if vertex not in outside or vertex in matched_vertices:
                raise ValueError(f"invalid matched vertex for cap {cap}")
            if slot not in SLOTS or slot in used_slots:
                raise ValueError(f"invalid or repeated slot for cap {cap}")
            if signature not in realized(cap, vertex, left_turns):
                raise ValueError(f"unrealized signature for cap {cap}")
            matched_vertices.add(vertex)
            used_slots.add(slot)

        hall_vertices = set(record.get("hall_vertices", []))
        if len(matched_vertices) == len(outside):
            if hall_vertices:
                raise ValueError(f"saturated cap {cap} has a Hall witness")
        else:
            if not hall_vertices or not hall_vertices <= outside:
                raise ValueError(f"invalid Hall vertex set for cap {cap}")
            neighbor_slots = {
                slot for vertex in hall_vertices for slot in SLOTS
                if slot[0] in realized(cap, vertex, left_turns)
            }
            deficiency = len(hall_vertices) - len(neighbor_slots)
            if deficiency <= 0:
                raise ValueError(f"Hall set for cap {cap} is not deficient")
            if len(matched_vertices) != len(outside) - deficiency:
                raise ValueError(f"matching/Hall bounds do not meet for cap {cap}")
        histogram[len(matched_vertices)] += 1

    if seen_caps != expected_caps:
        raise ValueError("certificate does not cover every crossing cap")
    expected_histogram = {str(key): value for key, value in sorted(histogram.items())}
    if certificate.get("matching_histogram") != expected_histogram:
        raise ValueError("matching histogram mismatch")
    if certificate.get("crossing_caps") != len(expected_caps):
        raise ValueError("crossing cap count mismatch")
    print(json.dumps({
        "checked_caps": len(expected_caps),
        "matching_histogram": expected_histogram,
        "model_sha256": certificate["model_sha256"],
    }, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    args = parser.parse_args()
    verify(args.model, args.certificate)


if __name__ == "__main__":
    main()
