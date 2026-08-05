#!/usr/bin/env python3
"""Certify cap-failure charge matching ranks in a validated sharp model.

Each outside vertex may realize several of the nine consecutive four-cap
failure signatures.  Two copies of every signature form the candidate charge
slots.  For every crossing four-cap, this script records a maximum matching
and a Hall-deficient vertex set when the matching is not saturating.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections import Counter, deque
from pathlib import Path

from generate_signotope_state_sat import git_revision, write_atomic


Signature = tuple[int, int]
Slot = tuple[Signature, int]

SIGNATURES: tuple[Signature, ...] = tuple(
    (gap, index)
    for gap in range(5)
    for index in range(3)
    if index <= gap <= index + 2
)
SLOTS: tuple[Slot, ...] = tuple(
    (signature, copy) for signature in SIGNATURES for copy in range(2)
)


def load_model(path: Path) -> tuple[dict[str, object], set[tuple[int, int, int]]]:
    data = json.loads(path.read_text())
    if data.get("schema_version") != 1:
        raise ValueError("model schema_version must be one")
    validation = data.get("validation")
    if not isinstance(validation, dict) or validation.get("valid") is not True:
        raise ValueError("model must carry a successful independent validation")
    n, cut = data.get("n"), data.get("cut")
    if not isinstance(n, int) or not isinstance(cut, int) or not 0 < cut < n:
        raise ValueError("model has invalid n or cut")
    left_turns = {tuple(triple) for triple in data.get("left_triples", [])}
    if any(len(triple) != 3 or tuple(sorted(triple)) != triple
           for triple in left_turns):
        raise ValueError("left_triples must contain sorted triples")
    return data, left_turns


def crossing_caps(n: int, cut: int, left_turns: set[tuple[int, int, int]]):
    return [
        cap for cap in itertools.combinations(range(n), 4)
        if min(cap) < cut <= max(cap)
        and all(triple not in left_turns
                for triple in itertools.combinations(cap, 3))
    ]


def realized_signatures(
    cap: tuple[int, ...], q: int,
    left_turns: set[tuple[int, int, int]],
) -> set[Signature]:
    five = tuple(sorted((*cap, q)))
    gap = five.index(q)
    return {
        (gap, index) for index in range(3)
        if index <= gap <= index + 2
        and five[index:index + 3] in left_turns
    }


def maximum_matching(
    vertices: tuple[int, ...], allowed: dict[int, set[Signature]],
) -> tuple[dict[int, Slot], set[int]]:
    slot_owner: dict[Slot, int] = {}
    vertex_slot: dict[int, Slot] = {}

    def augment(vertex: int, seen: set[Slot]) -> bool:
        for slot in SLOTS:
            if slot[0] not in allowed[vertex] or slot in seen:
                continue
            seen.add(slot)
            owner = slot_owner.get(slot)
            if owner is None or augment(owner, seen):
                slot_owner[slot] = vertex
                vertex_slot[vertex] = slot
                return True
        return False

    for vertex in vertices:
        augment(vertex, set())

    reached_vertices = set(vertices) - set(vertex_slot)
    reached_slots: set[Slot] = set()
    queue = deque(sorted(reached_vertices))
    while queue:
        vertex = queue.popleft()
        for slot in SLOTS:
            if slot[0] not in allowed[vertex] or vertex_slot.get(vertex) == slot:
                continue
            if slot in reached_slots:
                continue
            reached_slots.add(slot)
            owner = slot_owner.get(slot)
            if owner is not None and owner not in reached_vertices:
                reached_vertices.add(owner)
                queue.append(owner)

    if len(vertex_slot) < len(vertices):
        neighbors = {slot for vertex in reached_vertices for slot in SLOTS
                     if slot[0] in allowed[vertex]}
        if neighbors != reached_slots or len(neighbors) >= len(reached_vertices):
            raise RuntimeError("failed to derive a Hall-deficiency certificate")
    return vertex_slot, reached_vertices


def analyze(model_path: Path, output_path: Path) -> None:
    data, left_turns = load_model(model_path)
    n, cut = int(data["n"]), int(data["cut"])
    records = []
    histogram: Counter[int] = Counter()
    for cap in crossing_caps(n, cut, left_turns):
        vertices = tuple(vertex for vertex in range(n) if vertex not in cap)
        allowed = {vertex: realized_signatures(cap, vertex, left_turns)
                   for vertex in vertices}
        if any(not signatures for signatures in allowed.values()):
            raise RuntimeError(f"cap {cap} has an uncharged outside vertex")
        matching, hall_vertices = maximum_matching(vertices, allowed)
        histogram[len(matching)] += 1
        records.append({
            "cap": list(cap),
            "matching": [
                [vertex, slot[0][0], slot[0][1], slot[1]]
                for vertex, slot in sorted(matching.items())
            ],
            "hall_vertices": sorted(hall_vertices)
                if len(matching) < len(vertices) else [],
        })

    model_bytes = model_path.read_bytes()
    certificate = {
        "schema_version": 1,
        "generator": "scripts/analyze_cap_failure_charge_matching.py",
        "revision": git_revision(Path(__file__).resolve().parent.parent),
        "model": str(model_path),
        "model_sha256": hashlib.sha256(model_bytes).hexdigest(),
        "n": n,
        "cut": cut,
        "signature_count": len(SIGNATURES),
        "slot_count": len(SLOTS),
        "crossing_caps": len(records),
        "matching_histogram": dict(sorted(histogram.items())),
        "records": records,
    }
    write_atomic(output_path, json.dumps(certificate, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: certificate[key] for key in (
        "n", "cut", "signature_count", "slot_count", "crossing_caps",
        "matching_histogram")}, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    analyze(args.model, args.output)


if __name__ == "__main__":
    main()
