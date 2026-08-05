#!/usr/bin/env python3
"""Profile the five endpoint-anomaly classes in checked sharp models.

This is a deterministic falsification aid, not a proof producer.  A listed
triple in the input JSON is a left turn.  For every strong six-set on the
left side of the cut, the script computes which of the four internal anomaly
positions and the final-fan class are realized by each right-side vertex.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


def triples(vertices):
    return tuple(itertools.combinations(vertices, 3))


def is_strong(vertices, left_turns):
    for i, j, k, l in itertools.combinations(vertices, 4):
        if (((i, j, k) in left_turns) != ((i, j, l) in left_turns)):
            return False
        if (((i, k, l) in left_turns) != ((j, k, l) in left_turns)):
            return False
    return True


def anomaly_options(polygon, q, left_turns):
    result = []
    for position, j in enumerate(polygon[1:5]):
        reference = (polygon[0], j, polygon[5]) in left_turns
        if any(((i, j, q) in left_turns) != reference
               for i in polygon if i < j):
            result.append(f"I{position}")
    fan = [((i, polygon[5], q) in left_turns)
           for i in polygon if i < polygon[5]]
    if len(set(fan)) > 1:
        result.append("F")
    return tuple(result)


def admits_uniform_capacity(options, capacity):
    slots = [(label, copy) for label in ("I0", "I1", "I2", "I3", "F")
             for copy in range(capacity)]
    matched = {}

    def augment(vertex, seen):
        for slot in slots:
            if slot[0] not in options[vertex] or slot in seen:
                continue
            seen.add(slot)
            if slot not in matched or augment(matched[slot], seen):
                matched[slot] = vertex
                return True
        return False

    return all(augment(vertex, set()) for vertex in range(len(options)))


def profile_direction(n, cut, left_turns, direction):
    if direction == "right_strong":
        left_turns = {
            tuple(sorted(n - 1 - vertex for vertex in triple))
            for triple in left_turns
        }
        cut = n - cut
    polygons = []
    for polygon in itertools.combinations(range(cut), 6):
        if not is_strong(polygon, left_turns):
            continue
        options = [anomaly_options(polygon, q, left_turns)
                   for q in range(cut, n)]
        if any(not value for value in options):
            raise RuntimeError(
                f"unclassified endpoint failure for {polygon}")
        min_capacity = next(
            capacity for capacity in range(1, len(options) + 1)
            if admits_uniform_capacity(options, capacity))
        incidence = {
            label: sum(label in value for value in options)
            for label in ("I0", "I1", "I2", "I3", "F")
        }
        polygons.append({
            "polygon": polygon,
            "middle_signature": [
                "L" if (polygon[0], j, polygon[5]) in left_turns else "R"
                for j in polygon[1:5]
            ],
            "opposite_vertices": len(options),
            "minimum_uniform_assignment_capacity": min_capacity,
            "maximum_class_incidence": max(incidence.values()),
            "class_incidence": incidence,
            "option_masks": ["/".join(value) for value in options],
        })
    polygons.sort(key=lambda item: (
        item["minimum_uniform_assignment_capacity"],
        item["maximum_class_incidence"],
        item["polygon"],
    ))
    return {
        "direction": direction,
        "strong_sixes_on_left": len(polygons),
        "minimum_uniform_assignment_capacity_range": (
            [min(item["minimum_uniform_assignment_capacity"]
                 for item in polygons),
             max(item["minimum_uniform_assignment_capacity"]
                 for item in polygons)] if polygons else []),
        "maximum_class_incidence": (
            max(item["maximum_class_incidence"] for item in polygons)
            if polygons else 0),
        "most_constrained_examples": polygons[:5],
    }


def profile(path):
    data = json.loads(path.read_text())
    n = data["n"]
    cut = data["cut"]
    left_turns = {tuple(value) for value in data["left_triples"]}
    return {
        "model": str(path),
        "n": n,
        "cut": cut,
        "directions": [
            profile_direction(n, cut, left_turns, "left_strong"),
            profile_direction(n, cut, left_turns, "right_strong"),
        ],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("models", nargs="+", type=Path)
    args = parser.parse_args()
    print(json.dumps([profile(path) for path in args.models], indent=2))


if __name__ == "__main__":
    main()
