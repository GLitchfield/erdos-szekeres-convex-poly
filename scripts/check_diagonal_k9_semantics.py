#!/usr/bin/env python3
"""Independent audit of the generated k=9 semantic-certificate inputs.

This checker deliberately imports neither the Lean generator nor the original
CNF generator.  It reconstructs the source clause stream, identifies every
retained dense clause after undoing the variable map, and replays the RUP-only
LRAT proof.  It also runs a corrupted-final-hint negative control.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import itertools
import json
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator


N = 15


class AuditFailure(RuntimeError):
    pass


@dataclass(frozen=True)
class Case:
    tag: str
    left: int
    right: int
    variables: int
    clauses: int
    additions: int
    cnf_hash: str
    lrat_hash: str
    families: dict[str, int]


CASES = (
    Case(
        "78", 7, 8, 396, 1157, 812,
        "ed5d3604a251013d80716f2cff0f0d7eb34a81936bcf281792f39b56a839fe72",
        "47654921221546d883544620525cb98806238d65f112467f9ccfe10dfafa0c8a",
        {"quad": 1016, "cap": 26, "cup": 15, "strong": 9, "unit": 91},
    ),
    Case(
        "87", 8, 7, 280, 429, 239,
        "21c281818b3688488debe1d521b6f4b468c2d34a2d79db8a3a7962a7ab679d39",
        "150596401f45f9789deaba920e0e87690eceb5c68ad8524e2ac7611bd3544091",
        {"quad": 322, "cap": 8, "cup": 5, "strong": 3, "unit": 91},
    ),
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def triples(vertices) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(vertices, 3))


ALL_TRIPLES = triples(range(N))
VARIABLES = {triple: index + 1 for index, triple in enumerate(ALL_TRIPLES)}


def forbidden(
    keys: tuple[tuple[int, int, int], ...], values: tuple[bool, ...]
) -> tuple[int, ...]:
    return tuple(-VARIABLES[key] if value else VARIABLES[key] for key, value in zip(keys, values))


def independent_strong_patterns() -> tuple[tuple[bool, ...], ...]:
    """Enumerate the 128 middle-determined strong-nine assignments directly."""
    local = triples(range(9))
    return tuple(
        tuple(middle_colors[j] for _, j, _ in local)
        for middle_colors in itertools.product((False, True), repeat=7)
        for middle_colors in [(False, *middle_colors, False)]
    )


STRONG_PATTERNS = independent_strong_patterns()


def source_stream(case: Case) -> Iterator[tuple[tuple[int, ...], str]]:
    for vertices in itertools.combinations(range(N), 4):
        i, j, k, l = vertices
        keys = ((i, j, k), (i, j, l), (i, k, l), (j, k, l))
        for values in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(values, values[1:])) > 1:
                yield forbidden(keys, tuple(values)), "quad"
    for vertices in itertools.combinations(range(N), 4):
        yield tuple(VARIABLES[key] for key in triples(vertices)), "cap"
    for vertices in itertools.combinations(range(N), 9):
        yield tuple(-VARIABLES[key] for key in triples(vertices)), "cup"
    local = triples(range(9))
    for vertices in itertools.combinations(range(N), 9):
        keys = tuple(tuple(vertices[index] for index in triple) for triple in local)
        for values in STRONG_PATTERNS:
            yield forbidden(keys, values), "strong"
    for block in (range(case.left), range(case.left, N)):
        for triple in triples(block):
            yield (VARIABLES[triple],), "unit"


def parse_cnf(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variable_count = None
    declared = None
    clauses: list[tuple[int, ...]] = []
    current: list[int] = []
    for line_number, text in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        text = text.strip()
        if not text or text.startswith("c"):
            continue
        if text.startswith("p"):
            fields = text.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"] or variable_count is not None:
                raise AuditFailure(f"{path}:{line_number}: malformed header")
            variable_count, declared = int(fields[2]), int(fields[3])
            continue
        if variable_count is None:
            raise AuditFailure(f"{path}:{line_number}: clause before header")
        for field in text.split():
            literal = int(field)
            if literal == 0:
                clauses.append(tuple(current))
                current = []
            else:
                if abs(literal) > variable_count:
                    raise AuditFailure(f"{path}:{line_number}: literal out of range")
                current.append(literal)
    if variable_count is None or declared is None or current or len(clauses) != declared:
        raise AuditFailure(f"{path}: inconsistent clause count")
    return variable_count, clauses


def audit_clause_origins(repo: Path, run_dir: Path, case: Case) -> dict[str, int]:
    cnf_path = repo / "certificates" / f"k9-cup-blocks-{case.left}-{case.right}-dense.cnf"
    variables, dense_clauses = parse_cnf(cnf_path)
    map_path = run_dir / f"k9-{case.tag}-dense-variable-map.json"
    mapping = json.loads(map_path.read_text())
    old_variables = list(mapping["old_variable_ids"])
    if variables != case.variables or variables != len(old_variables) or len(dense_clauses) != case.clauses:
        raise AuditFailure(f"{case.tag}: dense shape mismatch")
    undensified = [
        tuple((1 if literal > 0 else -1) * old_variables[abs(literal) - 1] for literal in clause)
        for clause in dense_clauses
    ]
    wanted_counts = collections.Counter(undensified)
    wanted = set(wanted_counts)
    origins: dict[tuple[int, ...], collections.Counter[str]] = {}
    source_count = 0
    for clause, family in source_stream(case):
        source_count += 1
        if clause in wanted:
            origins.setdefault(clause, collections.Counter())[family] += 1
    if source_count != 658021:
        raise AuditFailure(f"{case.tag}: independently reconstructed source count is {source_count}")
    missing = wanted - origins.keys()
    if missing:
        raise AuditFailure(f"{case.tag}: {len(missing)} retained clauses have no semantic origin")
    families = tuple(case.families)
    expected = tuple(case.families[family] for family in families)

    def allocations(available: tuple[int, ...], total: int, index: int = 0):
        if index == len(available):
            if total == 0:
                yield ()
            return
        for count in range(min(available[index], total) + 1):
            for tail in allocations(available, total - count, index + 1):
                yield (count, *tail)

    possible = {tuple(0 for _ in families)}
    for clause, multiplicity in wanted_counts.items():
        available = tuple(origins[clause][family] for family in families)
        choices = tuple(allocations(available, multiplicity))
        if not choices:
            raise AuditFailure(f"{case.tag}: retained clause multiplicity exceeds source origins")
        next_possible = set()
        for subtotal in possible:
            for choice in choices:
                candidate = tuple(x + y for x, y in zip(subtotal, choice))
                if all(x <= y for x, y in zip(candidate, expected)):
                    next_possible.add(candidate)
        possible = next_possible
        if not possible:
            raise AuditFailure(f"{case.tag}: source-origin family counts are inconsistent")
    if expected not in possible:
        raise AuditFailure(f"{case.tag}: expected retained family multiset is unavailable")
    return dict(zip(families, expected))


def parse_lrat_record(text: str, line_number: int):
    fields = text.split()
    if len(fields) >= 2 and fields[1] == "d":
        if fields[-1] != "0":
            raise AuditFailure(f"LRAT line {line_number}: malformed deletion")
        return int(fields[0]), "d", tuple(map(int, fields[2:-1])), ()
    try:
        tokens = tuple(map(int, fields))
        first_zero = tokens.index(0, 1)
    except (ValueError, IndexError) as error:
        raise AuditFailure(f"LRAT line {line_number}: malformed addition") from error
    if not tokens[first_zero + 1 :] or tokens[-1] != 0:
        raise AuditFailure(f"LRAT line {line_number}: missing hint terminator")
    hints = tokens[first_zero + 1 : -1]
    if any(hint <= 0 for hint in hints):
        raise AuditFailure(f"LRAT line {line_number}: non-RUP hint")
    return tokens[0], "a", tokens[1:first_zero], hints


def assign(assignments: dict[int, bool], literal: int, context: str) -> None:
    variable, value = abs(literal), literal > 0
    old = assignments.get(variable)
    if old is not None and old != value:
        raise AuditFailure(f"{context}: inconsistent assignment")
    assignments[variable] = value


def replay_lrat(cnf_path: Path, lrat_path: Path, corrupt_empty_hint: bool = False) -> dict[str, int]:
    _, original_clauses = parse_cnf(cnf_path)
    original_count = len(original_clauses)
    active = {index: clause for index, clause in enumerate(original_clauses, 1)}
    derived: set[int] = set()
    additions = 0
    deletions = 0
    empty_clause_id = None
    for line_number, text in enumerate(lrat_path.read_text(encoding="ascii").splitlines(), 1):
        clause_id, kind, payload, hints = parse_lrat_record(text, line_number)
        if kind == "d":
            deletions += 1
            for deleted in payload:
                if deleted > original_count and deleted not in derived:
                    raise AuditFailure(f"LRAT line {line_number}: unknown deletion")
                active.pop(deleted, None)
            continue
        additions += 1
        if clause_id <= original_count or clause_id in derived:
            raise AuditFailure(f"LRAT line {line_number}: nonfresh clause")
        if corrupt_empty_hint and not payload:
            hints = (clause_id + 1_000_000, *hints[1:]) if hints else (clause_id + 1_000_000,)
        assignments: dict[int, bool] = {}
        for literal in payload:
            assign(assignments, -literal, f"LRAT line {line_number}")
        conflict = False
        for hint in hints:
            clause = active.get(hint)
            if clause is None:
                raise AuditFailure(f"LRAT line {line_number}: unavailable hint {hint}")
            unassigned: list[int] = []
            satisfied = False
            for literal in clause:
                value = assignments.get(abs(literal))
                if value is None:
                    unassigned.append(literal)
                elif value == (literal > 0):
                    satisfied = True
                    break
            if satisfied or len(unassigned) > 1:
                raise AuditFailure(f"LRAT line {line_number}: hint is not unit/conflicting")
            if not unassigned:
                conflict = True
                break
            assign(assignments, unassigned[0], f"LRAT line {line_number}")
        if not conflict:
            raise AuditFailure(f"LRAT line {line_number}: RUP chain has no conflict")
        active[clause_id] = payload
        derived.add(clause_id)
        if not payload:
            empty_clause_id = clause_id
    if empty_clause_id is None:
        raise AuditFailure("LRAT did not derive the empty clause")
    return {"additions": additions, "deletions": deletions, "empty_clause_id": empty_clause_id}


def audit_case(repo: Path, run_dir: Path, case: Case) -> dict[str, object]:
    cnf = repo / "certificates" / f"k9-cup-blocks-{case.left}-{case.right}-dense.cnf"
    lrat = repo / "certificates" / f"k9-cup-blocks-{case.left}-{case.right}-dense.lrat"
    if digest(cnf) != case.cnf_hash or digest(lrat) != case.lrat_hash:
        raise AuditFailure(f"{case.tag}: dense artifact hash mismatch")
    families = audit_clause_origins(repo, run_dir, case)
    replay = replay_lrat(cnf, lrat)
    if replay["additions"] != case.additions:
        raise AuditFailure(f"{case.tag}: LRAT addition count mismatch")
    negative_rejected = False
    try:
        replay_lrat(cnf, lrat, corrupt_empty_hint=True)
    except AuditFailure:
        negative_rejected = True
    if not negative_rejected:
        raise AuditFailure(f"{case.tag}: corrupted-hint control was accepted")
    return {
        "orientation": f"{case.left}+{case.right}",
        "cnf_sha256": case.cnf_hash,
        "lrat_sha256": case.lrat_hash,
        "variables": case.variables,
        "clauses": case.clauses,
        "family_counts": families,
        "lrat_replay": replay,
        "corrupted_final_hint_rejected": True,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument(
        "--source-run",
        type=Path,
        default=Path("runs/agents/20260810-three-route-forward/state567"),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("runs/agents/20260810-parallel-portfolio/k9/independent-audit.json"),
    )
    args = parser.parse_args()
    repo = args.repo.resolve()
    run_dir = args.source_run if args.source_run.is_absolute() else repo / args.source_run
    output = args.output if args.output.is_absolute() else repo / args.output
    started = time.monotonic()
    try:
        cases = [audit_case(repo, run_dir, case) for case in CASES]
    except AuditFailure as error:
        print(json.dumps({"status": "REJECTED", "reason": str(error)}, sort_keys=True))
        return 1
    result = {
        "schema_version": 1,
        "status": "VERIFIED",
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "cases": cases,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
