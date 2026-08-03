#!/usr/bin/env python3
"""Measure learned-clause dependencies crossing candidate LRAT segments.

This is a planning tool, not a proof checker.  It parses each LRAT addition,
records the segment in which a learned clause is introduced, and records the
last segment in which that clause is referenced by an addition proof.  A
learned clause must be exported across a boundary exactly when it was added on
or before that boundary and is referenced after it.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("lrat", type=Path)
    parser.add_argument("--original-clauses", type=int, required=True)
    parser.add_argument("--segments", type=int, default=16)
    args = parser.parse_args()
    if args.segments < 2:
        parser.error("--segments must be at least two")

    size = args.lrat.stat().st_size
    add_segment: dict[int, int] = {}
    last_reference: dict[int, int] = {}
    segment_lines = [0] * args.segments
    segment_additions = [0] * args.segments
    segment_deletions = [0] * args.segments
    negative_references = 0
    final_empty_id: int | None = None

    with args.lrat.open("rb") as source:
        while True:
            offset = source.tell()
            raw = source.readline()
            if not raw:
                break
            segment = min(args.segments - 1, offset * args.segments // size)
            segment_lines[segment] += 1
            fields = raw.split()
            if not fields:
                continue
            clause_id = int(fields[0])
            if len(fields) >= 2 and fields[1] == b"d":
                segment_deletions[segment] += 1
                continue
            segment_additions[segment] += 1
            try:
                first_zero = fields.index(b"0", 1)
                second_zero = fields.index(b"0", first_zero + 1)
            except ValueError as exc:
                raise ValueError(f"unterminated LRAT line at byte {offset}") from exc
            literals = fields[1:first_zero]
            if not literals:
                final_empty_id = clause_id
            for token in fields[first_zero + 1:second_zero]:
                reference = int(token)
                if reference < 0:
                    negative_references += 1
                    reference = -reference
                if reference > args.original_clauses:
                    last_reference[reference] = segment
            add_segment[clause_id] = segment

    boundaries = []
    for boundary in range(args.segments - 1):
        crossing = [
            clause_id
            for clause_id, introduced in add_segment.items()
            if introduced <= boundary < last_reference.get(clause_id, introduced)
        ]
        boundaries.append({
            "after_segment": boundary,
            "crossing_learned_clauses": len(crossing),
            "minimum_id": min(crossing) if crossing else None,
            "maximum_id": max(crossing) if crossing else None,
        })

    exported_unique = sum(
        last_reference.get(clause_id, introduced) > introduced
        for clause_id, introduced in add_segment.items()
    )

    print(json.dumps({
        "lrat": str(args.lrat),
        "bytes": size,
        "segments": args.segments,
        "original_clauses": args.original_clauses,
        "learned_additions": len(add_segment),
        "final_empty_id": final_empty_id,
        "negative_references": negative_references,
        "learned_clauses_exported_once": exported_unique,
        "segment_lines": segment_lines,
        "segment_additions": segment_additions,
        "segment_deletions": segment_deletions,
        "boundaries": boundaries,
    }, indent=2))


if __name__ == "__main__":
    main()
