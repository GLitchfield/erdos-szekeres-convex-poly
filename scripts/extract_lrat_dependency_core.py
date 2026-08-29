#!/usr/bin/env python3
"""Extract and densely renumber a positive-hint LRAT dependency core.

Unlike the older Fin11-local extractor, this implementation accepts ordinary
LRAT deletion rows.  It scans the proof backwards, retaining only additions in
the transitive dependency cone of the final empty clause.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def reverse_lines(path: Path, block_size: int = 8 * 1024 * 1024):
    with path.open("rb") as stream:
        position = stream.seek(0, 2)
        remainder = b""
        while position:
            take = min(block_size, position)
            position -= take
            stream.seek(position)
            block = stream.read(take) + remainder
            pieces = block.split(b"\n")
            remainder = pieces[0]
            for line in reversed(pieces[1:]):
                if line:
                    yield line
        if remainder:
            yield remainder


def parse_cnf(path: Path) -> tuple[int, list[list[int]]]:
    variables = 0
    expected = -1
    clauses: list[list[int]] = []
    with path.open() as stream:
        for raw in stream:
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p"):
                _, kind, variable_text, clause_text = line.split()
                if kind != "cnf":
                    raise ValueError("expected DIMACS CNF")
                variables = int(variable_text)
                expected = int(clause_text)
                continue
            values = [int(piece) for piece in line.split()]
            if not values or values[-1] != 0:
                raise ValueError("unterminated DIMACS clause")
            clauses.append(values[:-1])
    if variables <= 0 or len(clauses) != expected:
        raise ValueError("DIMACS header mismatch")
    return variables, clauses


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def extract(cnf: Path, lrat: Path, output_dir: Path) -> dict[str, object]:
    variables, base_clauses = parse_cnf(cnf)
    base_count = len(base_clauses)
    needed: set[int] = set()
    selected: dict[int, tuple[list[int], list[int]]] = {}
    additions_seen = 0
    deletion_lines_seen = 0
    final_id = None

    for raw in reverse_lines(lrat):
        fields = raw.split()
        if len(fields) < 2:
            raise ValueError("malformed LRAT line")
        if fields[1] == b"d":
            if fields[-1] != b"0":
                raise ValueError("unterminated LRAT deletion")
            deletion_lines_seen += 1
            continue
        additions_seen += 1
        clause_id = int(fields[0])
        if final_id is None:
            final_id = clause_id
            needed.add(clause_id)
        if clause_id not in needed:
            continue
        try:
            first_zero = fields.index(b"0", 1)
            second_zero = fields.index(b"0", first_zero + 1)
        except ValueError as error:
            raise ValueError(f"malformed LRAT clause {clause_id}") from error
        if second_zero != len(fields) - 1:
            raise ValueError(f"unexpected LRAT tail at clause {clause_id}")
        clause = [int(piece) for piece in fields[1:first_zero]]
        hints = [int(piece) for piece in fields[first_zero + 1:second_zero]]
        if any(hint <= 0 or hint >= clause_id for hint in hints):
            raise ValueError(f"non-positive or forward hint at clause {clause_id}")
        selected[clause_id] = (clause, hints)
        needed.update(hints)

    if final_id is None or final_id not in selected:
        raise ValueError("empty LRAT input")
    if selected[final_id][0]:
        raise ValueError("last LRAT addition is not empty")
    unresolved = sorted(item for item in needed if item > base_count and item not in selected)
    if unresolved:
        raise ValueError(f"unresolved addition dependencies: {unresolved[:5]}")
    selected_base_ids = sorted(item for item in needed if item <= base_count)
    selected_addition_ids = sorted(selected)

    variables_used = {
        abs(literal)
        for old_id in selected_base_ids
        for literal in base_clauses[old_id - 1]
    }
    variables_used.update(
        abs(literal)
        for old_id in selected_addition_ids
        for literal in selected[old_id][0]
    )
    if any(variable <= 0 or variable > variables for variable in variables_used):
        raise ValueError("out-of-range variable in selected core")
    variable_map = {old: new for new, old in enumerate(sorted(variables_used), start=1)}
    clause_order = selected_base_ids + selected_addition_ids
    clause_map = {old: new for new, old in enumerate(clause_order, start=1)}

    output_dir.mkdir(parents=True, exist_ok=True)
    core_cnf = output_dir / "core.cnf"
    core_lrat = output_dir / "core.lrat"
    with core_cnf.open("w") as output:
        output.write(f"p cnf {len(variable_map)} {len(selected_base_ids)}\n")
        for old_id in selected_base_ids:
            mapped = [
                (-1 if literal < 0 else 1) * variable_map[abs(literal)]
                for literal in base_clauses[old_id - 1]
            ]
            output.write(" ".join(map(str, mapped)) + " 0\n")
    with core_lrat.open("w") as output:
        for old_id in selected_addition_ids:
            clause, hints = selected[old_id]
            mapped_clause = [
                (-1 if literal < 0 else 1) * variable_map[abs(literal)]
                for literal in clause
            ]
            mapped_hints = [clause_map[hint] for hint in hints]
            output.write(
                " ".join(
                    map(str, [clause_map[old_id], *mapped_clause, 0, *mapped_hints, 0])
                )
                + "\n"
            )

    metadata: dict[str, object] = {
        "schema_version": 1,
        "source": {
            "cnf": str(cnf),
            "cnf_sha256": digest(cnf),
            "lrat": str(lrat),
            "lrat_sha256": digest(lrat),
            "variables": variables,
            "base_clauses": base_count,
            "additions": additions_seen,
            "deletion_lines": deletion_lines_seen,
            "final_clause_id": final_id,
        },
        "core": {
            "variables": len(variable_map),
            "base_clauses": len(selected_base_ids),
            "additions": len(selected_addition_ids),
            "final_clause_id": len(clause_order),
            "cnf_sha256": digest(core_cnf),
            "lrat_sha256": digest(core_lrat),
        },
        "selected_base_ids": selected_base_ids,
        "selected_addition_ids": selected_addition_ids,
        "variable_map_old_to_new": variable_map,
    }
    (output_dir / "core-map.json").write_text(
        json.dumps(metadata, indent=2, sort_keys=True) + "\n"
    )
    return metadata


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf", type=Path)
    parser.add_argument("lrat", type=Path)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()
    metadata = extract(args.cnf, args.lrat, args.output_dir)
    print(json.dumps(metadata["core"], sort_keys=True))


if __name__ == "__main__":
    main()
