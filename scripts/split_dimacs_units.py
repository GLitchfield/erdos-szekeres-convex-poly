#!/usr/bin/env python3
"""Split a DIMACS instance into exhaustive unit-assignment branches."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path


def parse_dimacs(path: Path) -> tuple[int, list[str]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    comments = [line for line in lines if line.startswith("c")]
    headers = [line for line in lines if line.startswith("p cnf ")]
    if len(headers) != 1:
        raise ValueError("expected exactly one DIMACS header")
    _, _, variable_text, clause_text = headers[0].split()
    clauses = [line for line in lines if line and not line.startswith(("c", "p"))]
    if len(clauses) != int(clause_text):
        raise ValueError(f"header declares {clause_text} clauses, parsed {len(clauses)}")
    for clause in clauses:
        if clause.split()[-1] != "0":
            raise ValueError(f"unterminated clause: {clause[:80]}")
    return int(variable_text), comments + clauses


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output_directory", type=Path)
    parser.add_argument("--variables", required=True,
                        help="comma-separated one-based DIMACS variables")
    parser.add_argument("--prefix", default="branch")
    args = parser.parse_args()

    variable_count, body = parse_dimacs(args.input)
    variables = [int(value) for value in args.variables.split(",")]
    if not variables or len(set(variables)) != len(variables):
        parser.error("variables must be a nonempty list without duplicates")
    if min(variables) < 1 or max(variables) > variable_count:
        parser.error("branch variable is outside the DIMACS range")

    comments = [line for line in body if line.startswith("c")]
    clauses = [line for line in body if not line.startswith("c")]
    args.output_directory.mkdir(parents=True, exist_ok=True)
    for bits in itertools.product((False, True), repeat=len(variables)):
        suffix = "".join("1" if bit else "0" for bit in bits)
        units = [f"{variable if bit else -variable} 0"
                 for variable, bit in zip(variables, bits)]
        output = args.output_directory / f"{args.prefix}-{suffix}.cnf"
        content = comments + [f"p cnf {variable_count} {len(clauses) + len(units)}"]
        content.extend(clauses)
        content.extend(units)
        output.write_text("\n".join(content) + "\n", encoding="utf-8")
    print(f"branches={2 ** len(variables)} variables={variables} "
          f"directory={args.output_directory}")


if __name__ == "__main__":
    main()
