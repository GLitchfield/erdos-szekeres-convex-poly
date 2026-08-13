#!/usr/bin/env python3
"""Independently audit the frozen Fin11 cube manifest and positive-hint LRATs."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path


EXPECTED_SOURCE_SHA256 = "50cf18bc1b14ad5c6ded5086a0437e664cdda4411c686f70c55ac6455070ab13"
EXPECTED_SOURCE_VARIABLES = 1881
EXPECTED_SOURCE_CLAUSES = 19207
EXPECTED_SPLIT_VARIABLES = (83, 84)
ALTERNATE_SPLIT_VARIABLES = (15, 111)
RECURSIVE_SPLIT_VARIABLES = (
    (15, 111, 155),
    (15, 111, 155, 68),
    (15, 111, 155, 68, 142),
    (15, 111, 155, 68, 142, 2),
)


class AuditFailure(RuntimeError):
    pass


def sha256(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(1024 * 1024):
            result.update(block)
    return result.hexdigest()


def parse_cnf(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = 0
    expected_clauses = -1
    clauses: list[tuple[int, ...]] = []
    header_seen = False
    with path.open("r", encoding="ascii") as stream:
        for line_number, raw in enumerate(stream, start=1):
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p"):
                fields = line.split()
                if header_seen or clauses or len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                    raise AuditFailure(f"{path}:{line_number}: bad DIMACS header")
                variables = int(fields[2])
                expected_clauses = int(fields[3])
                header_seen = True
                continue
            if not header_seen:
                raise AuditFailure(f"{path}:{line_number}: clause before header")
            fields = [int(field) for field in line.split()]
            if not fields or fields[-1] != 0 or 0 in fields[:-1]:
                raise AuditFailure(f"{path}:{line_number}: bad clause terminator")
            clause = tuple(fields[:-1])
            if any(literal == 0 or abs(literal) > variables for literal in clause):
                raise AuditFailure(f"{path}:{line_number}: out-of-range literal")
            clauses.append(clause)
    if not header_seen or variables <= 0 or len(clauses) != expected_clauses:
        raise AuditFailure(f"{path}: DIMACS header mismatch")
    return variables, clauses


def expected_assignments(split_variables: tuple[int, ...]) -> set[tuple[int, ...]]:
    return {
        tuple(variable if bit else -variable for variable, bit in zip(split_variables, bits))
        for bits in itertools.product((0, 1), repeat=len(split_variables))
    }


def validate_source_record(source: dict[str, object], source_cnf: Path) -> None:
    expected = {
        "sha256": EXPECTED_SOURCE_SHA256,
        "variables": EXPECTED_SOURCE_VARIABLES,
        "clauses": EXPECTED_SOURCE_CLAUSES,
    }
    for key, value in expected.items():
        if source.get(key) != value:
            raise AuditFailure(f"manifest source {key} does not match the frozen value")
    if sha256(source_cnf) != EXPECTED_SOURCE_SHA256:
        raise AuditFailure("source CNF byte hash does not match the frozen value")


def validate_exhaustive_branches(
    branches: list[dict[str, object]],
    split_variables: tuple[int, ...],
) -> None:
    expected = expected_assignments(split_variables)
    observed: list[tuple[int, ...]] = []
    for branch in branches:
        units = tuple(branch.get("unit_literals", []))
        if len(units) != len(split_variables):
            raise AuditFailure("cube branch has the wrong number of unit literals")
        if tuple(abs(literal) for literal in units) != split_variables:
            raise AuditFailure("cube units do not use the frozen split variables in order")
        assignment = branch.get("assignment")
        expected_dictionary = {str(abs(literal)): literal > 0 for literal in units}
        if assignment != expected_dictionary:
            raise AuditFailure("assignment metadata disagrees with unit literals")
        observed.append(units)
    branch_count = 2 ** len(split_variables)
    if (
        len(branches) != branch_count
        or len(set(observed)) != branch_count
        or set(observed) != expected
    ):
        raise AuditFailure("cube manifest is not the exact exhaustive split")


def validate_children(
    output: Path,
    source_variables: int,
    source_clauses: list[tuple[int, ...]],
    branches: list[dict[str, object]],
) -> None:
    for branch in branches:
        child_path = output / branch["cnf"]
        variables, clauses = parse_cnf(child_path)
        expected_units = [(literal,) for literal in branch["unit_literals"]]
        expected = [*source_clauses, *expected_units]
        if variables != source_variables or clauses != expected:
            raise AuditFailure(f"{branch['name']}: child is not the exact source plus cube units")
        if branch.get("cnf_sha256") != sha256(child_path):
            raise AuditFailure(f"{branch['name']}: child CNF hash mismatch")
        if branch.get("base_clauses") != len(expected):
            raise AuditFailure(f"{branch['name']}: child base-clause count mismatch")


def literal_value(literal: int, assignments: dict[int, bool]) -> int:
    variable = abs(literal)
    if variable not in assignments:
        return 0
    value = assignments[variable]
    return 1 if value == (literal > 0) else -1


def enqueue(literal: int, assignments: dict[int, bool]) -> bool:
    variable = abs(literal)
    value = literal > 0
    current = assignments.get(variable)
    if current is not None:
        return current == value
    assignments[variable] = value
    return True


def check_addition(
    candidate: tuple[int, ...],
    hints: tuple[int, ...],
    clauses: list[tuple[int, ...]],
) -> bool:
    assignments: dict[int, bool] = {}
    for literal in candidate:
        if not enqueue(-literal, assignments):
            return not hints
    conflict = False
    for position, hint in enumerate(hints):
        if hint <= 0 or hint >= len(clauses):
            return False
        unassigned = 0
        unit = 0
        satisfied = False
        for literal in clauses[hint]:
            value = literal_value(literal, assignments)
            if value > 0:
                satisfied = True
                break
            if value == 0:
                unassigned += 1
                unit = literal
                if unassigned > 1:
                    break
        if satisfied or unassigned > 1:
            return False
        if unassigned == 0:
            conflict = True
            if position + 1 != len(hints):
                return False
            break
        if not enqueue(unit, assignments):
            return False
    return conflict


def replay_lrat(
    cnf_path: Path,
    lrat_path: Path,
    corrupt_final_hint: bool = False,
) -> dict[str, int | bool]:
    variables, base_clauses = parse_cnf(cnf_path)
    clauses: list[tuple[int, ...]] = [(), *base_clauses]
    additions = 0
    hint_edges = 0
    ended = False
    pending: tuple[int, tuple[int, ...], tuple[int, ...], int] | None = None

    def consume(row: tuple[int, tuple[int, ...], tuple[int, ...], int], corrupt: bool) -> None:
        nonlocal additions, hint_edges, ended
        clause_id, candidate, hints, line_number = row
        if ended or clause_id != len(clauses):
            raise AuditFailure(f"{lrat_path}:{line_number}: non-dense clause id or trailing row")
        if any(literal == 0 or abs(literal) > variables for literal in candidate):
            raise AuditFailure(f"{lrat_path}:{line_number}: out-of-range candidate literal")
        checked_hints = hints[:-1] if corrupt and hints else hints
        if not check_addition(candidate, checked_hints, clauses):
            raise AuditFailure(f"{lrat_path}:{line_number}: strict positive-hint replay failed")
        clauses.append(candidate)
        additions += 1
        hint_edges += len(checked_hints)
        ended = not candidate

    with lrat_path.open("r", encoding="ascii") as stream:
        for line_number, raw in enumerate(stream, start=1):
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            fields = [int(field) for field in line.split()]
            try:
                clause_end = fields.index(0, 1)
                hints_end = fields.index(0, clause_end + 1)
            except (ValueError, IndexError) as error:
                raise AuditFailure(f"{lrat_path}:{line_number}: malformed LRAT row") from error
            if hints_end != len(fields) - 1:
                raise AuditFailure(f"{lrat_path}:{line_number}: deletion tail is forbidden")
            candidate = tuple(fields[1:clause_end])
            hints = tuple(fields[clause_end + 1:hints_end])
            if any(hint <= 0 or hint >= fields[0] for hint in hints):
                raise AuditFailure(f"{lrat_path}:{line_number}: non-positive or forward hint")
            current = (fields[0], candidate, hints, line_number)
            if pending is not None:
                consume(pending, False)
            pending = current
    if pending is None:
        raise AuditFailure(f"{lrat_path}: empty LRAT proof")
    consume(pending, corrupt_final_hint)
    if not ended:
        raise AuditFailure(f"{lrat_path}: proof does not end in the empty clause")
    return {
        "additions": additions,
        "hint_edges": hint_edges,
        "ends_in_empty_clause": ended,
        "bytes": lrat_path.stat().st_size,
    }


def validate_proofs(output: Path, branches: list[dict[str, object]]) -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    for branch in branches:
        if branch.get("status") != "certified" or "proof" not in branch:
            raise AuditFailure(f"{branch['name']}: proof was required but is not certified")
        proof = branch["proof"]
        core_cnf = output / proof["core_cnf"]
        core_lrat = output / proof["core_lrat"]
        expected_hashes = {
            "core_cnf_sha256": sha256(core_cnf),
            "core_lrat_sha256": sha256(core_lrat),
            "core_map_sha256": sha256(output / proof["core_map"]),
        }
        if not proof.get("full_artifacts_pruned"):
            expected_hashes["rup_sha256"] = sha256(output / proof["rup"])
            expected_hashes["lrat_sha256"] = sha256(output / proof["lrat"])
        for key, value in expected_hashes.items():
            if proof.get(key) != value:
                raise AuditFailure(f"{branch['name']}: {key} mismatch")
        metrics = replay_lrat(core_cnf, core_lrat)
        for key in ("additions", "hint_edges", "ends_in_empty_clause", "bytes"):
            if proof.get(key) != metrics[key]:
                raise AuditFailure(f"{branch['name']}: {key} metric mismatch")
        results.append({"branch": branch["name"], **metrics})
    return results


def negative_controls(
    manifest: dict[str, object],
    source_cnf: Path,
    output: Path,
    split_variables: tuple[int, ...],
    require_proofs: bool,
) -> dict[str, bool]:
    controls: dict[str, bool] = {}
    wrong_source = dict(manifest["source"])
    wrong_source["sha256"] = "0" * 64
    try:
        validate_source_record(wrong_source, source_cnf)
    except AuditFailure:
        controls["changed_semantic_hash_rejected"] = True
    else:
        raise AuditFailure("changed semantic hash was accepted")

    omitted = list(manifest["branches"][:-1])
    try:
        validate_exhaustive_branches(omitted, split_variables)
    except AuditFailure:
        controls["omitted_cube_branch_rejected"] = True
    else:
        raise AuditFailure("omitted cube branch was accepted")

    wrong_unit = [dict(branch) for branch in manifest["branches"]]
    wrong_unit[0]["unit_literals"] = list(split_variables)
    try:
        validate_exhaustive_branches(wrong_unit, split_variables)
    except AuditFailure:
        controls["wrong_cube_unit_rejected"] = True
    else:
        raise AuditFailure("wrong cube unit was accepted")

    if require_proofs:
        branch = min(manifest["branches"], key=lambda item: item["proof"]["bytes"])
        proof = branch["proof"]
        try:
            replay_lrat(
                output / proof["core_cnf"],
                output / proof["core_lrat"],
                corrupt_final_hint=True,
            )
        except AuditFailure:
            controls["corrupt_final_hint_rejected"] = True
        else:
            raise AuditFailure("corrupt final LRAT hint was accepted")
    return controls


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--manifest",
        type=Path,
        default=Path("runs/agents/20260812-promotion-wave/fin11-cubes/manifest.json"),
    )
    parser.add_argument("--require-proofs", action="store_true")
    parser.add_argument("--expected-split-variable", type=int, action="append")
    args = parser.parse_args()

    manifest_path = args.manifest.resolve()
    output = manifest_path.parent
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema_version") != 1:
        raise AuditFailure("manifest schema_version must be one")
    split_variables = tuple(args.expected_split_variable or EXPECTED_SPLIT_VARIABLES)
    allowed_splits = (EXPECTED_SPLIT_VARIABLES, ALTERNATE_SPLIT_VARIABLES, *RECURSIVE_SPLIT_VARIABLES)
    if split_variables not in allowed_splits:
        raise AuditFailure("requested split variables are not a frozen Fin11 cube depth")
    if tuple(manifest.get("split", {}).get("variables", [])) != split_variables:
        raise AuditFailure("manifest split variables do not match the requested frozen pair")
    source_cnf = Path(manifest["source"]["path"])
    if not source_cnf.is_absolute():
        source_cnf = (Path.cwd() / source_cnf).resolve()
    validate_source_record(manifest["source"], source_cnf)
    variables, source_clauses = parse_cnf(source_cnf)
    validate_exhaustive_branches(manifest["branches"], split_variables)
    validate_children(output, variables, source_clauses, manifest["branches"])
    proofs = validate_proofs(output, manifest["branches"]) if args.require_proofs else []
    controls = negative_controls(
        manifest,
        source_cnf,
        output,
        split_variables,
        args.require_proofs,
    )
    result = {
        "schema_version": 1,
        "status": "passed",
        "source_sha256": sha256(source_cnf),
        "branch_count": len(manifest["branches"]),
        "proofs": proofs,
        "negative_controls": controls,
    }
    check_path = output / "independent-check.json"
    check_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
