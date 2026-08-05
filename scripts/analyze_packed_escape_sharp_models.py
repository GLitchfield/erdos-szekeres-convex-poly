#!/usr/bin/env python3
"""Census deletion packing and crossing splits in sharp 21-point models.

This is a cheap route-selection gate for the proposed packed middle-split
escape lemma.  It does not prove anything from an UNSAT result.  A model that
satisfies full packing but has a deletion covered only by middle crossing
strong sixes would, however, refute the size-generic escape contract.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from generate_signotope_state_sat import git_revision, write_atomic


def triples(vertices):
    return itertools.combinations(vertices, 3)


def is_strong(vertices, left_turns) -> bool:
    for i, j, k, l in itertools.combinations(vertices, 4):
        if ((i, j, k) in left_turns) != ((i, j, l) in left_turns):
            return False
        if ((i, k, l) in left_turns) != ((j, k, l) in left_turns):
            return False
    return True


def mask(vertices) -> int:
    result = 0
    for vertex in vertices:
        result |= 1 << vertex
    return result


def census(path: Path) -> dict[str, object]:
    raw = path.read_bytes()
    data = json.loads(raw)
    n = int(data["n"])
    cut = int(data["cut"])
    if n != 21:
        raise ValueError(f"{path}: expected a sharp 21-point model, got n={n}")
    left_turns = {tuple(item) for item in data["left_triples"]}
    expected = set(triples(range(n)))
    if not left_turns <= expected:
        raise ValueError(f"{path}: contains an invalid triple")

    strong = []
    split_counts = {str(index): 0 for index in range(7)}
    for vertices in itertools.combinations(range(n), 6):
        if is_strong(vertices, left_turns):
            vertices_mask = mask(vertices)
            split = sum(vertex < cut for vertex in vertices)
            strong.append((vertices, vertices_mask, split))
            split_counts[str(split)] += 1

    all_strong_masks = [entry[1] for entry in strong]
    extreme_masks = [entry[1] for entry in strong if entry[2] in (1, 5)]
    middle_masks = [entry[1] for entry in strong if entry[2] in (2, 3, 4)]
    packing_covered = 0
    extreme_covered = 0
    middle_only = []
    uncovered = []
    for deleted in itertools.combinations(range(n), 6):
        deleted_mask = mask(deleted)
        has_any = any(not (deleted_mask & witness) for witness in all_strong_masks)
        has_extreme = any(not (deleted_mask & witness) for witness in extreme_masks)
        has_middle = any(not (deleted_mask & witness) for witness in middle_masks)
        packing_covered += has_any
        extreme_covered += has_extreme
        if has_middle and not has_extreme:
            middle_only.append(deleted)
        if not has_any:
            uncovered.append(deleted)

    deletion_count = sum(1 for _ in itertools.combinations(range(n), 6))
    return {
        "path": str(path),
        "model_sha256": hashlib.sha256(raw).hexdigest(),
        "n": n,
        "cut": cut,
        "left_turn_triples": len(left_turns),
        "strong_sixes": len(strong),
        "split_counts": split_counts,
        "deletions": deletion_count,
        "packing_covered_deletions": packing_covered,
        "extreme_covered_deletions": extreme_covered,
        "full_packing": packing_covered == deletion_count,
        "full_extreme_packing": extreme_covered == deletion_count,
        "uncovered_deletion_count": len(uncovered),
        "uncovered_deletion_examples": [list(item) for item in uncovered[:10]],
        "middle_only_deletion_count": len(middle_only),
        "middle_only_deletion_examples": [list(item) for item in middle_only[:10]],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("models", nargs="+", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = {
        "schema_version": 1,
        "analyzer": "scripts/analyze_packed_escape_sharp_models.py",
        "revision": git_revision(Path(__file__).resolve().parent.parent),
        "models": [census(path) for path in args.models],
        "evidence_ceiling": "route-selection census; not a Lean proof",
    }
    write_atomic(args.output, json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
