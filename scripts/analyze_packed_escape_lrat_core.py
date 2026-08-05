#!/usr/bin/env python3
"""Trace the original-clause core of a packed-escape LRAT proof backwards.

The scan is streaming: learned-clause dependencies are discovered from the
empty clause while the large proof is read in reverse, so the full LRAT graph
is never resident in memory.  This is a planning aid, not a proof checker.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

from generate_signotope_state_sat import write_atomic


CATEGORY_ORDER = (
    "signotope",
    "side_cap",
    "no_cap",
    "no_cup",
    "xor_definitions",
    "strong_six_definitions",
    "no_internal_strong_six",
    "no_strong_seven",
    "packing",
    "select_bad_deletion",
    "selected_deletion_no_extreme",
)


def reverse_lines(path: Path, block_size: int = 8 * 1024 * 1024):
    with path.open("rb") as source:
        position = source.seek(0, 2)
        remainder = b""
        while position:
            amount = min(block_size, position)
            position -= amount
            source.seek(position)
            chunk = source.read(amount) + remainder
            parts = chunk.split(b"\n")
            remainder = parts[0]
            for line in reversed(parts[1:]):
                if line:
                    yield line
        if remainder:
            yield remainder


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("lrat", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument(
        "--clause-map", type=Path,
        help="optional new-to-original clause map for a previously reduced CNF",
    )
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    counts = manifest["clause_counts"]
    source_original_clauses = int(manifest["clauses"])
    if args.clause_map:
        clause_map = json.loads(args.clause_map.read_text())["old_clause_ids"]
    else:
        clause_map = list(range(1, source_original_clauses + 1))
    proof_original_clauses = len(clause_map)

    ranges = {}
    cursor = 1
    for category in CATEGORY_ORDER:
        count = int(counts.get(category, 0))
        ranges[category] = (cursor, cursor + count - 1)
        cursor += count
    if cursor - 1 != source_original_clauses:
        raise SystemExit(
            f"clause categories sum to {cursor - 1}, "
            f"expected {source_original_clauses}"
        )

    needed = set()
    original_core = set()
    learned_used = 0
    final_empty_id = None
    for raw in reverse_lines(args.lrat):
        fields = raw.split()
        if len(fields) < 2 or fields[1] == b"d":
            continue
        clause_id = int(fields[0])
        first_zero = fields.index(b"0", 1)
        if final_empty_id is None:
            if first_zero != 1:
                continue
            final_empty_id = clause_id
            needed.add(clause_id)
        if clause_id not in needed:
            continue
        needed.remove(clause_id)
        learned_used += 1
        try:
            second_zero = fields.index(b"0", first_zero + 1)
        except ValueError as error:
            raise SystemExit(f"unterminated hint list at LRAT clause {clause_id}") from error
        for token in fields[first_zero + 1:second_zero]:
            reference = abs(int(token))
            if reference <= proof_original_clauses:
                original_core.add(int(clause_map[reference - 1]))
            else:
                needed.add(reference)
    if final_empty_id is None:
        raise SystemExit("LRAT contains no final empty clause")
    if needed:
        raise SystemExit(f"missing {len(needed)} learned dependencies")

    category_ids = {}
    for category, (first, last) in ranges.items():
        category_ids[category] = sorted(
            clause_id for clause_id in original_core if first <= clause_id <= last
        )

    n = int(manifest["parameters"]["n"])
    cut = int(manifest["parameters"]["cut"])
    packing_first = ranges["packing"][0]
    sixes = tuple(itertools.combinations(range(n), 6))
    packing_deletions = [
        sixes[clause_id - packing_first]
        for clause_id in category_ids["packing"]
    ]
    split_counts = {str(index): 0 for index in range(7)}
    for deleted in packing_deletions:
        split_counts[str(sum(vertex < cut for vertex in deleted))] += 1

    result = {
        "schema_version": 1,
        "analyzer": "scripts/analyze_packed_escape_lrat_core.py",
        "lrat": str(args.lrat),
        "lrat_bytes": args.lrat.stat().st_size,
        "lrat_sha256": sha256(args.lrat),
        "manifest": str(args.manifest),
        "source_original_clauses": source_original_clauses,
        "proof_original_clauses": proof_original_clauses,
        "clause_map": str(args.clause_map) if args.clause_map else None,
        "final_empty_id": final_empty_id,
        "learned_clauses_in_dependency_core": learned_used,
        "original_core_clauses": len(original_core),
        "original_core_ids": sorted(original_core),
        "category_core_counts": {
            category: len(category_ids[category]) for category in CATEGORY_ORDER
        },
        "packing_core_count": len(packing_deletions),
        "packing_core_split_counts": split_counts,
        "packing_core_deletions": [list(item) for item in packing_deletions],
        "evidence_ceiling": "LRAT dependency planning aid; not independently checked here",
    }
    write_atomic(args.output, json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        key: result[key] for key in (
            "original_core_clauses",
            "learned_clauses_in_dependency_core",
            "packing_core_count",
            "packing_core_split_counts",
        )
    }, sort_keys=True))


if __name__ == "__main__":
    main()
