#!/usr/bin/env python3
"""Extract a dependency-selected original-clause core from a DIMACS file."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from generate_signotope_state_sat import write_atomic


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf", type=Path)
    parser.add_argument("core", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--map-output", required=True, type=Path)
    args = parser.parse_args()
    core = json.loads(args.core.read_text())
    selected = list(core["original_core_ids"])
    selected_set = set(selected)
    if len(selected_set) != len(selected):
        raise SystemExit("core contains duplicate clause identifiers")

    variables = None
    clauses = []
    clause_id = 0
    for raw in args.cnf.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p "):
            fields = line.split()
            variables = int(fields[2])
            continue
        clause_id += 1
        if clause_id in selected_set:
            clauses.append(line)
    if variables is None:
        raise SystemExit("missing DIMACS header")
    if clause_id < max(selected, default=0) or len(clauses) != len(selected):
        raise SystemExit("core references a missing DIMACS clause")
    content = f"p cnf {variables} {len(clauses)}\n" + "\n".join(clauses) + "\n"
    write_atomic(args.output, content)
    write_atomic(args.map_output, json.dumps({
        "schema_version": 1,
        "source_cnf": str(args.cnf),
        "old_clause_ids": selected,
    }, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "variables": variables,
        "source_clauses": clause_id,
        "core_clauses": len(clauses),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
