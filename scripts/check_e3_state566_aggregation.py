#!/usr/bin/env python3
"""Independently check the generated E3 state-566 aggregation hierarchy.

This checker deliberately does not import either Lean generator.  It reads the
canonical DIMACS file and the generated Lean text, reconstructs the expected
balanced proposition trees, and checks every raw and midpoint module plus the
root elimination tree.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import re
from pathlib import Path


N = 16
BASE_COUNT = 256
RAW_PER_BASE = 16
RAW_PER_MID = 4
PREFIX = "E3State566"


def parse_dimacs(path: Path) -> tuple[int, list[list[int]]]:
    tokens: list[int] = []
    variable_count = clause_count = None
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("c"):
            continue
        if stripped.startswith("p "):
            fields = stripped.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                raise ValueError("invalid DIMACS header")
            variable_count, clause_count = map(int, fields[2:])
            continue
        tokens.extend(map(int, stripped.split()))
    if variable_count is None or clause_count is None:
        raise ValueError("missing DIMACS header")
    clauses: list[list[int]] = []
    current: list[int] = []
    for token in tokens:
        if token == 0:
            if not current:
                raise ValueError("empty or duplicated DIMACS clause terminator")
            clauses.append(current)
            current = []
        else:
            if abs(token) > variable_count:
                raise ValueError(f"literal {token} exceeds declared variable count")
            current.append(token)
    if current:
        raise ValueError("unterminated DIMACS clause")
    if len(clauses) != clause_count:
        raise ValueError(
            f"DIMACS declares {clause_count} clauses but contains {len(clauses)}"
        )
    return variable_count, clauses


def split_ranges(start: int, stop: int, count: int) -> list[tuple[int, int]]:
    """Independently reproduce a balanced binary partition into ``count`` leaves."""
    if count == 1:
        return [(start, stop)]
    if count <= 0 or count % 2 or stop - start < count:
        raise ValueError("invalid balanced range partition")
    midpoint = start + (stop - start) // 2
    half = count // 2
    return split_ranges(start, midpoint, half) + split_ranges(midpoint, stop, half)


def balanced(items: list[str], operator: str) -> str:
    if not items:
        raise ValueError("cannot render an empty proposition")
    if len(items) == 1:
        return items[0]
    midpoint = len(items) // 2
    return (
        f"({balanced(items[:midpoint], operator)} {operator} "
        f"{balanced(items[midpoint:], operator)})"
    )


def triple_term(triple: tuple[int, int, int]) -> str:
    a, b, c = triple
    return f"(χ ⟨{a}, {b}, {c}, by decide, by decide⟩ = Turn.left)"


def bad_clause(clause: list[int], triples: list[tuple[int, int, int]]) -> str:
    literals = [
        ("¬" if literal > 0 else "") + triple_term(triples[abs(literal) - 1])
        for literal in clause
    ]
    return "(" + " ∧ ".join(literals) + ")"


def theorem_bad_expression(text: str) -> str:
    marker = ") : ¬ ("
    start = text.find(marker)
    if start < 0:
        raise ValueError("generated theorem has no negated aggregation result")
    start += len(marker)
    stop = text.find(") := by", start)
    if stop < 0:
        raise ValueError("generated theorem result is unterminated")
    return text[start:stop]


def expected_refutation(indices: list[int]) -> str:
    if len(indices) == 1:
        return f"h{indices[0]} hbad"
    midpoint = len(indices) // 2
    return (
        "(Or.elim hbad "
        f"(fun hbad ↦ {expected_refutation(indices[:midpoint])}) "
        f"(fun hbad ↦ {expected_refutation(indices[midpoint:])}))"
    )


def check_exact(label: str, actual: object, expected: object) -> None:
    if actual != expected:
        raise ValueError(f"{label} does not match the independently reconstructed value")


def check_hierarchy(repo: Path) -> None:
    cnf_path = repo / "certificates/e3-signotope-16-5-6-6.cnf"
    variable_count, clauses = parse_dimacs(cnf_path)
    triples = list(itertools.combinations(range(N), 3))
    check_exact("DIMACS variable count", variable_count, len(triples))

    metadata = json.loads(
        (repo / "certificates/e3-state566-checkpoints/metadata.json").read_text()
    )
    check_exact("checkpoint CNF path", metadata["cnf"], str(cnf_path.relative_to(repo)))
    check_exact("checkpoint clause count", metadata["original_clauses"], len(clauses))
    check_exact(
        "checkpoint CNF digest",
        metadata["cnf_sha256"],
        hashlib.sha256(cnf_path.read_bytes()).hexdigest(),
    )
    context = (repo / "ErdosSzekeres/E3State566CheckpointContext.lean").read_text()
    if 'include_str "../certificates/e3-signotope-16-5-6-6.cnf"' not in context:
        raise ValueError("checkpoint context does not include the canonical CNF")

    clause_props = [bad_clause(clause, triples) for clause in clauses]
    base_ranges = split_ranges(0, len(clauses), BASE_COUNT)
    raw_ranges = [
        subrange
        for start, stop in base_ranges
        for subrange in split_ranges(start, stop, RAW_PER_BASE)
    ]
    mid_ranges = [
        subrange
        for start, stop in base_ranges
        for subrange in split_ranges(start, stop, RAW_PER_BASE // RAW_PER_MID)
    ]
    check_exact("raw module count", len(raw_ranges), 4096)
    check_exact("midpoint module count", len(mid_ranges), 1024)

    lean_dir = repo / "ErdosSzekeres"
    for index, (start, stop) in enumerate(raw_ranges):
        path = lean_dir / f"{PREFIX}CNFRaw{index:04}.lean"
        text = path.read_text(encoding="utf-8")
        expected = balanced(clause_props[start:stop], "∨")
        check_exact(f"raw proposition {index}", theorem_bad_expression(text), expected)

    for index, (start, stop) in enumerate(mid_ranges):
        path = lean_dir / f"{PREFIX}CNFMid{index:04}.lean"
        text = path.read_text(encoding="utf-8")
        expected = balanced(clause_props[start:stop], "∨")
        check_exact(f"midpoint proposition {index}", theorem_bad_expression(text), expected)
        raw_indices = list(range(index * RAW_PER_MID, (index + 1) * RAW_PER_MID))
        imports = [
            int(value)
            for value in re.findall(
                r"^import ErdosSzekeres\.E3State566CNFRaw(\d{4})$",
                text,
                re.MULTILINE,
            )
        ]
        check_exact(f"midpoint raw imports {index}", imports, raw_indices)
        leaves = [int(value) for value in re.findall(r"h(\d+) hbad", text)]
        check_exact(f"midpoint elimination leaves {index}", leaves, raw_indices)

    named = (lean_dir / f"{PREFIX}CNFMidNamed.lean").read_text(encoding="utf-8")
    imports = [
        int(value)
        for value in re.findall(
            r"^public import ErdosSzekeres\.E3State566CNFMid(\d{4})$",
            named,
            re.MULTILINE,
        )
    ]
    check_exact("named midpoint imports", imports, list(range(len(mid_ranges))))
    aliases = [
        tuple(map(int, values))
        for values in re.findall(
            r"negated_conclusion_alias E3State566BadMid(\d+) "
            r"e3State566CNFNamedMid(\d+)_of_constraints from "
            r"e3State566CNFMid(\d+)_of_constraints",
            named,
        )
    ]
    check_exact(
        "named midpoint aliases",
        aliases,
        [(index, index, index) for index in range(len(mid_ranges))],
    )

    named_root = (lean_dir / f"{PREFIX}CNFNamedRoot.lean").read_text(encoding="utf-8")
    definition_marker = f"def {PREFIX}BadMidTree (χ : TripleColoring {N}) : Prop :=\n  "
    definition_start = named_root.find(definition_marker)
    if definition_start < 0:
        raise ValueError("named root has no midpoint-tree definition")
    definition_start += len(definition_marker)
    definition_stop = named_root.find("\n\ntheorem ", definition_start)
    if definition_stop < 0:
        raise ValueError("named midpoint-tree definition is unterminated")
    check_exact(
        "named midpoint tree",
        named_root[definition_start:definition_stop],
        balanced([f"{PREFIX}BadMid{index} χ" for index in range(len(mid_ranges))], "∨"),
    )
    hypothesis_pairs = [
        tuple(map(int, values))
        for values in re.findall(
            r"have h(\d+) := e3State566CNFNamedMid(\d+)_of_constraints",
            named_root,
        )
    ]
    check_exact(
        "named root hypotheses",
        hypothesis_pairs,
        [(index, index) for index in range(len(mid_ranges))],
    )
    last_exact = named_root.rfind("  exact ")
    if last_exact < 0:
        raise ValueError("named root theorem has no final exact term")
    actual_refutation = named_root[last_exact + len("  exact "):].splitlines()[0]
    check_exact(
        "named root elimination tree",
        actual_refutation,
        expected_refutation(list(range(len(mid_ranges)))),
    )

    bridge = (lean_dir / f"{PREFIX}CNFNamedBridge.lean").read_text(encoding="utf-8")
    expected_bridge = (
        f"{PREFIX}Bad χ = {PREFIX}BadMidTree χ := by\n"
        "  rfl"
    )
    if expected_bridge not in bridge:
        raise ValueError("named bridge is not the expected definitional equality proof")
    semantics = (lean_dir / f"{PREFIX}CNFSemantics.lean").read_text(encoding="utf-8")
    if f"public import ErdosSzekeres.{PREFIX}CNFNamedBridge" not in semantics:
        raise ValueError("semantic theorem does not import the checked named bridge")
    if "(e3State566Bad_eq_badMidTree χ).mp hbad" not in semantics:
        raise ValueError("semantic theorem does not transport through the named bridge")

    print(
        f"checked clauses={len(clauses)} raw={len(raw_ranges)} "
        f"midpoints={len(mid_ranges)} cnf_sha256={metadata['cnf_sha256']}"
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="independently check the E3 state-566 Lean aggregation hierarchy"
    )
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    check_hierarchy(args.repo.resolve())


if __name__ == "__main__":
    main()
