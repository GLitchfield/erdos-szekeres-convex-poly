#!/usr/bin/env python3
"""Independently check the generated E3 state-455 aggregation hierarchy."""

from __future__ import annotations

import hashlib
import itertools
import json
import re
from pathlib import Path


N = 8
CHUNK_COUNT = 8
PREFIX = "E3State455"
EXPECTED_CNF_SHA256 = "56ea4a13b8f976fbb266ef58e8a8c7074de38e08a201fda0477b59642abc49c1"
EXPECTED_LRAT_SHA256 = "5401621fc275e55a42077cecd293b5b303969da341bd6a0dc25973eaf5287861"


def parse_dimacs(path: Path) -> tuple[int, list[list[int]]]:
    variables = declared_clauses = None
    tokens: list[int] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("c"):
            continue
        if stripped.startswith("p "):
            fields = stripped.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                raise ValueError("invalid DIMACS header")
            variables, declared_clauses = map(int, fields[2:])
        else:
            tokens.extend(map(int, stripped.split()))
    if variables is None or declared_clauses is None:
        raise ValueError("missing DIMACS header")
    clauses: list[list[int]] = []
    clause: list[int] = []
    for token in tokens:
        if token == 0:
            if not clause:
                raise ValueError("empty DIMACS clause")
            clauses.append(clause)
            clause = []
        else:
            if abs(token) > variables:
                raise ValueError(f"literal {token} exceeds the variable count")
            clause.append(token)
    if clause:
        raise ValueError("unterminated DIMACS clause")
    if len(clauses) != declared_clauses:
        raise ValueError("DIMACS clause count mismatch")
    return variables, clauses


def balanced(items: list[str], operator: str) -> str:
    if len(items) == 1:
        return items[0]
    if not items:
        raise ValueError("cannot balance an empty list")
    midpoint = len(items) // 2
    return (
        f"({balanced(items[:midpoint], operator)} {operator} "
        f"{balanced(items[midpoint:], operator)})"
    )


def split_balanced(items: list[str], count: int) -> list[list[str]]:
    if count == 1:
        return [items]
    midpoint = len(items) // 2
    half = count // 2
    return split_balanced(items[:midpoint], half) + split_balanced(items[midpoint:], half)


def triple_term(triple: tuple[int, int, int]) -> str:
    a, b, c = triple
    return f"(χ ⟨{a}, {b}, {c}, by decide, by decide⟩ = Turn.left)"


def bad_clause(clause: list[int], triples: list[tuple[int, int, int]]) -> str:
    literals = [
        ("¬" if literal > 0 else "") + triple_term(triples[abs(literal) - 1])
        for literal in clause
    ]
    return "(" + " ∧ ".join(literals) + ")"


def definition_body(text: str, declaration: str) -> str:
    marker = declaration + " :=\n    "
    start = text.find(marker)
    if start < 0:
        raise ValueError(f"missing declaration {declaration}")
    start += len(marker)
    stop = text.find("\n\n", start)
    if stop < 0:
        raise ValueError(f"unterminated declaration {declaration}")
    return text[start:stop]


def check(repo: Path) -> None:
    certificate_dir = repo / "certificates"
    lean_dir = repo / "ErdosSzekeres"
    cnf_path = certificate_dir / "e3-signotope-8-4-5-5.cnf"
    lrat_path = certificate_dir / "e3-signotope-8-4-5-5.lrat"
    metadata = json.loads((cnf_path.with_suffix(".cnf.json")).read_text())
    cnf_hash = hashlib.sha256(cnf_path.read_bytes()).hexdigest()
    lrat_hash = hashlib.sha256(lrat_path.read_bytes()).hexdigest()
    if cnf_hash != EXPECTED_CNF_SHA256 or metadata["cnf_sha256"] != cnf_hash:
        raise ValueError("canonical CNF digest mismatch")
    if lrat_hash != EXPECTED_LRAT_SHA256:
        raise ValueError("canonical LRAT digest mismatch")
    variables, clauses = parse_dimacs(cnf_path)
    if (variables, len(clauses)) != (56, 1134):
        raise ValueError("unexpected canonical DIMACS dimensions")
    expected_metadata = {
        "n": 8,
        "cap": 4,
        "cup": 5,
        "strong": 5,
        "variables": 56,
        "clauses": 1134,
        "strong_pattern_count": 8,
        "clause_counts": {
            "signotope": 560,
            "no_cap": 70,
            "no_cup": 56,
            "no_strong": 448,
        },
    }
    for key, value in expected_metadata.items():
        if metadata.get(key) != value:
            raise ValueError(f"metadata field {key} mismatch")

    triples = list(itertools.combinations(range(N), 3))
    expected_clauses = [bad_clause(clause, triples) for clause in clauses]
    expected_chunks = split_balanced(expected_clauses, CHUNK_COUNT)
    for index, chunk in enumerate(expected_chunks):
        path = lean_dir / f"{PREFIX}CNFChunk{index:02}.lean"
        text = path.read_text(encoding="utf-8")
        declaration = f"def {PREFIX}BadChunk{index} (χ : TripleColoring {N}) : Prop"
        if definition_body(text, declaration) != balanced(chunk, "∨"):
            raise ValueError(f"chunk proposition {index} mismatch")
        if text.count(f"theorem e3State455CNFChunk{index}_of_constraints") != 1:
            raise ValueError(f"chunk theorem {index} missing or duplicated")

    root = (lean_dir / f"{PREFIX}CNFGenerated.lean").read_text(encoding="utf-8")
    imports = [
        int(index)
        for index in re.findall(
            rf"^public import ErdosSzekeres\.{PREFIX}CNFChunk(\d{{2}})$",
            root,
            re.MULTILINE,
        )
    ]
    if imports != list(range(CHUNK_COUNT)):
        raise ValueError("root imports do not cover every chunk exactly once")
    root_declaration = f"def {PREFIX}Bad (χ : TripleColoring {N}) : Prop"
    expected_root = balanced(
        [f"{PREFIX}BadChunk{index} χ" for index in range(CHUNK_COUNT)], "∨"
    )
    if definition_body(root, root_declaration) != expected_root:
        raise ValueError("root proposition mismatch")
    if "have hcertificate := e3State455_cnf_unsat" not in root:
        raise ValueError("root does not use the kernel-checked LRAT theorem")
    if root.count("have h") < CHUNK_COUNT:
        raise ValueError("root does not collect every semantic chunk")

    unsat = (lean_dir / f"{PREFIX}Unsat.lean").read_text(encoding="utf-8")
    for relative in (
        "../certificates/e3-signotope-8-4-5-5.cnf",
        "../certificates/e3-signotope-8-4-5-5.lrat",
    ):
        if f'include_str "{relative}"' not in unsat:
            raise ValueError(f"LRAT module does not include {relative}")

    print(
        f"checked clauses={len(clauses)} chunks={CHUNK_COUNT} "
        f"cnf_sha256={cnf_hash} lrat_sha256={lrat_hash}"
    )


def main() -> None:
    check(Path(__file__).resolve().parent.parent)


if __name__ == "__main__":
    main()
