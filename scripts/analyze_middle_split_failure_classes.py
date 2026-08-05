#!/usr/bin/env python3
"""Classify normalized middle failures in the checked crossing-pair model.

This analyzer consumes an already independently validated model. It does not
certify the model or prove that a reported class is forced in every model.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

from verify_middle_split_pair_model import CUT, FIRST, N, SECOND, parse_model, triples


def color(left_turns, a, b, c):
    return (a, b, c) in left_turns


def has_left_anomaly(polygon, q, left_turns):
    first, last = polygon[0], polygon[-1]
    for middle in polygon[1:-1]:
        reference = color(left_turns, first, middle, last)
        if q < middle and color(left_turns, q, middle, last) != reference:
            return True
    return False


def has_right_anomaly(polygon, q, left_turns):
    first, last = polygon[0], polygon[-1]
    for middle in polygon[1:-1]:
        reference = color(left_turns, first, middle, last)
        if middle < q and color(left_turns, first, middle, q) != reference:
            return True
    return False


def has_left_internal_fan(polygon, q, left_turns):
    for middle in polygon[1:-1]:
        later = [vertex for vertex in polygon if middle < vertex]
        values = {color(left_turns, q, middle, vertex) for vertex in later if q < middle}
        if len(values) > 1:
            return True
    return False


def has_right_internal_fan(polygon, q, left_turns):
    for middle in polygon[1:-1]:
        earlier = [vertex for vertex in polygon if vertex < middle]
        values = {color(left_turns, vertex, middle, q) for vertex in earlier if middle < q}
        if len(values) > 1:
            return True
    return False


def has_fresh_middle_fan(polygon, q, left_turns):
    earlier = [vertex for vertex in polygon if vertex < q]
    later = [vertex for vertex in polygon if q < vertex]
    values = {
        color(left_turns, left, q, right)
        for left, right in itertools.product(earlier, later)
    }
    return len(values) > 1


def has_first_fan(polygon, q, left_turns):
    first = polygon[0]
    values = {
        color(left_turns, q, first, later)
        for later in polygon
        if q < first < later
    }
    return len(values) > 1


def has_final_fan(polygon, q, left_turns):
    last = polygon[-1]
    values = {
        color(left_turns, earlier, last, q)
        for earlier in polygon
        if earlier < last < q
    }
    return len(values) > 1


def classes(polygon, q, left_turns):
    common = {
        "left_anomaly": has_left_anomaly(polygon, q, left_turns),
        "fresh_middle_fan": has_fresh_middle_fan(polygon, q, left_turns),
        "right_anomaly": has_right_anomaly(polygon, q, left_turns),
    }
    if q < CUT:
        candidates = {
            **common,
            "first_fan": has_first_fan(polygon, q, left_turns),
            "left_internal_fan": has_left_internal_fan(polygon, q, left_turns),
            "right_internal_fan": has_right_internal_fan(polygon, q, left_turns),
        }
    else:
        candidates = {
            **common,
            "left_internal_fan": has_left_internal_fan(polygon, q, left_turns),
            "right_internal_fan": has_right_internal_fan(polygon, q, left_turns),
            "final_fan": has_final_fan(polygon, q, left_turns),
        }
    return sorted(label for label, realized in candidates.items() if realized)


def internal_positions(polygon, q, left_turns):
    first, last = polygon[0], polygon[-1]
    result = {
        "left_anomaly": set(),
        "left_internal_fan": set(),
        "right_anomaly": set(),
        "right_internal_fan": set(),
    }
    for rank, middle in enumerate(polygon[1:-1]):
        reference = color(left_turns, first, middle, last)
        later = [vertex for vertex in polygon if middle < vertex]
        earlier = [vertex for vertex in polygon if vertex < middle]
        if q < middle and color(left_turns, q, middle, last) != reference:
            result["left_anomaly"].add(rank)
        left_values = {
            color(left_turns, q, middle, vertex)
            for vertex in later
            if q < middle
        }
        if len(left_values) > 1:
            result["left_internal_fan"].add(rank)
        if middle < q and color(left_turns, first, middle, q) != reference:
            result["right_anomaly"].add(rank)
        right_values = {
            color(left_turns, vertex, middle, q)
            for vertex in earlier
            if middle < q
        }
        if len(right_values) > 1:
            result["right_internal_fan"].add(rank)
    return {label: sorted(ranks) for label, ranks in result.items() if ranks}


def validate_canonical_bridge_transitions(polygon, q, left_turns, positions):
    first, last = polygon[0], polygon[-1]
    checked = []
    for rank in positions.get("left_anomaly", []):
        middle = polygon[rank + 1]
        if first < q < middle:
            reference = color(left_turns, first, middle, last)
            if color(left_turns, first, q, middle) != reference:
                raise SystemExit("canonical left anomaly bridge failure")
            if color(left_turns, first, q, last) != reference:
                raise SystemExit("canonical left anomaly long bridge failure")
            checked.append(f"left:{rank}")
    for rank in positions.get("right_anomaly", []):
        middle = polygon[rank + 1]
        if middle < q < last:
            reference = color(left_turns, first, middle, last)
            if color(left_turns, first, q, last) != reference:
                raise SystemExit("canonical right anomaly long bridge failure")
            if color(left_turns, middle, q, last) != reference:
                raise SystemExit("canonical right anomaly bridge failure")
            checked.append(f"right:{rank}")
    return checked


def bridge_certificates(polygon, q, left_turns):
    certificates = []
    for frame in itertools.combinations(polygon, 3):
        quad = tuple(sorted((*frame, q)))
        sequence = [
            color(left_turns, *triple)
            for triple in itertools.combinations(quad, 3)
        ]
        position = quad.index(q)
        for kind, realized in (
            ("head", sequence[0] == sequence[1] == sequence[2]),
            ("tail", sequence[1] == sequence[2] == sequence[3]),
        ):
            if realized:
                certificates.append({
                    "frame": frame,
                    "kind": kind,
                    "position": position,
                    "anchored": position in (1, 2),
                })
    return certificates


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("model", type=Path)
    args = parser.parse_args()
    all_triples = triples(range(N))
    true_variables = parse_model(args.model, len(all_triples))
    left_turns = {
        triple
        for index, triple in enumerate(all_triples, start=1)
        if index in true_variables
    }
    profiles = []
    anchored_by_direction = {}
    for reference, probes in ((FIRST, SECOND), (SECOND, FIRST)):
        for q in probes:
            realized = classes(reference, q, left_turns)
            if not realized:
                raise SystemExit(f"no normalized failure class for {reference=} {q=}")
            positions = internal_positions(reference, q, left_turns)
            certificates = bridge_certificates(reference, q, left_turns)
            anchored_frames = {
                tuple(certificate["frame"])
                for certificate in certificates
                if certificate["anchored"]
            }
            anchored_by_direction[tuple(reference), q] = anchored_frames
            profiles.append({
                "reference": reference,
                "probe": q,
                "classes": realized,
                "internal_positions": positions,
                "bridge_checks": validate_canonical_bridge_transitions(
                    reference, q, left_turns, positions
                ),
                "bridge_certificate_count": len(certificates),
                "anchored_frames": sorted(anchored_frames),
            })
    shared_anchored_pairs = []
    for reference, probes in ((FIRST, SECOND), (SECOND, FIRST)):
        for q0, q1 in itertools.combinations(probes, 2):
            shared = sorted(
                anchored_by_direction[tuple(reference), q0]
                & anchored_by_direction[tuple(reference), q1]
            )
            for x, y, z in shared:
                if color(left_turns, x, q0, z) != color(left_turns, x, q1, z):
                    raise SystemExit("shared anchored frame color disagreement")
            if shared:
                shared_anchored_pairs.append({
                    "reference": reference,
                    "probes": (q0, q1),
                    "frames": shared,
                })
    print(json.dumps({
        "profiles": profiles,
        "shared_anchored_pairs": shared_anchored_pairs,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
