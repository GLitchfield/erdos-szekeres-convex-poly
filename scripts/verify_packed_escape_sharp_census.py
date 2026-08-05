#!/usr/bin/env python3
"""Independently replay a sharp-model deletion-packing census."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


def is_strong(vertices, left_turns) -> bool:
    for i, j, k, l in itertools.combinations(vertices, 4):
        if ((i, j, k) in left_turns) != ((i, j, l) in left_turns):
            return False
        if ((i, k, l) in left_turns) != ((j, k, l) in left_turns):
            return False
    return True


def vertex_mask(vertices) -> int:
    value = 0
    for vertex in vertices:
        value |= 1 << vertex
    return value


def replay(entry) -> dict[str, object]:
    path = Path(entry["path"])
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != entry["model_sha256"]:
        raise SystemExit(f"model hash mismatch: {path}")
    model = json.loads(raw)
    n = int(model["n"])
    cut = int(model["cut"])
    colors = {tuple(item) for item in model["left_triples"]}
    candidates = list(itertools.combinations(range(n), 6))
    strong = [vertices for vertices in candidates if is_strong(vertices, colors)]
    by_split = {str(index): 0 for index in range(7)}
    for vertices in strong:
        by_split[str(sum(vertex < cut for vertex in vertices))] += 1
    strong_masks = [vertex_mask(vertices) for vertices in strong]
    extreme_masks = [
        vertex_mask(vertices) for vertices in strong
        if sum(vertex < cut for vertex in vertices) in (1, 5)
    ]
    middle_masks = [
        vertex_mask(vertices) for vertices in strong
        if sum(vertex < cut for vertex in vertices) in (2, 3, 4)
    ]
    uncovered = []
    middle_only = []
    extreme_covered = 0
    for deleted in candidates:
        deleted_mask = vertex_mask(deleted)
        has_any = any(deleted_mask & witness == 0 for witness in strong_masks)
        has_extreme = any(deleted_mask & witness == 0 for witness in extreme_masks)
        has_middle = any(deleted_mask & witness == 0 for witness in middle_masks)
        extreme_covered += has_extreme
        if not has_any:
            uncovered.append(deleted)
        if has_middle and not has_extreme:
            middle_only.append(deleted)
    checks = {
        "n": n,
        "cut": cut,
        "left_turn_triples": len(colors),
        "strong_sixes": len(strong),
        "split_counts": by_split,
        "deletions": len(candidates),
        "packing_covered_deletions": len(candidates) - len(uncovered),
        "extreme_covered_deletions": extreme_covered,
        "full_packing": not uncovered,
        "full_extreme_packing": extreme_covered == len(candidates),
        "uncovered_deletion_count": len(uncovered),
        "uncovered_deletion_examples": [list(item) for item in uncovered[:10]],
        "middle_only_deletion_count": len(middle_only),
        "middle_only_deletion_examples": [list(item) for item in middle_only[:10]],
    }
    for key, value in checks.items():
        if entry.get(key) != value:
            raise SystemExit(
                f"census mismatch for {path}, field {key}: "
                f"recorded={entry.get(key)!r}, replayed={value!r}"
            )
    return {"path": str(path), "valid": True}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("census", type=Path)
    args = parser.parse_args()
    data = json.loads(args.census.read_text())
    results = [replay(entry) for entry in data["models"]]
    print(json.dumps({"valid": True, "models": results}, sort_keys=True))


if __name__ == "__main__":
    main()
