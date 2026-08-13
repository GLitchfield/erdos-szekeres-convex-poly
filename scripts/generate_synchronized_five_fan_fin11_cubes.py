#!/usr/bin/env python3
"""Prepare and, when explicitly requested, certify the frozen Fin11 cube gate."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import resource
import subprocess
import sys
import time
from pathlib import Path


EXPECTED_SOURCE_SHA256 = "50cf18bc1b14ad5c6ded5086a0437e664cdda4411c686f70c55ac6455070ab13"
EXPECTED_SOURCE_VARIABLES = 1881
EXPECTED_SOURCE_CLAUSES = 19207
INITIAL_SPLIT_VARIABLES = (83, 84)
ALTERNATE_SPLIT_VARIABLES = (15, 111)
RECURSIVE_SPLIT_VARIABLES = (
    (15, 111, 155),
    (15, 111, 155, 68),
    (15, 111, 155, 68, 142),
    (15, 111, 155, 68, 142, 2),
)

PROCESS_SECONDS = 30 * 60
PROCESS_MEMORY_BYTES = 16 * 1024**3
OUTPUT_BYTES = 5 * 1024**3
INITIAL_COMBINED_BYTES = 1536 * 1024**2
INITIAL_MAX_ADDITIONS = 150_000
INITIAL_MAX_HINT_EDGES = 5_000_000
FINAL_MAX_ADDITIONS = 25_000
FINAL_MAX_HINT_EDGES = 750_000
FINAL_MAX_BASE_CLAUSES = 8_000
FINAL_MAX_LRAT_BYTES = 64 * 1024**2


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
                if header_seen or clauses:
                    raise ValueError(f"{path}:{line_number}: misplaced duplicate DIMACS header")
                fields = line.split()
                if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                    raise ValueError(f"{path}:{line_number}: invalid DIMACS header")
                variables = int(fields[2])
                expected_clauses = int(fields[3])
                header_seen = True
                continue
            if not header_seen:
                raise ValueError(f"{path}:{line_number}: clause before DIMACS header")
            fields = [int(field) for field in line.split()]
            if not fields or fields[-1] != 0 or 0 in fields[:-1]:
                raise ValueError(f"{path}:{line_number}: malformed DIMACS clause")
            clause = tuple(fields[:-1])
            if any(abs(literal) > variables for literal in clause):
                raise ValueError(f"{path}:{line_number}: out-of-range literal")
            clauses.append(clause)
    if not header_seen or variables <= 0 or len(clauses) != expected_clauses:
        raise ValueError(f"{path}: DIMACS header mismatch")
    return variables, clauses


def write_cnf(path: Path, variables: int, clauses: list[tuple[int, ...]]) -> None:
    rows = [f"p cnf {variables} {len(clauses)}"]
    rows.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    content = "\n".join(rows) + "\n"
    if path.exists() and path.read_text(encoding="ascii") == content:
        return
    path.write_text(content, encoding="ascii")


def branch_name(assignment: tuple[int, ...]) -> str:
    parts = [f"v{abs(literal):03d}-{1 if literal > 0 else 0}" for literal in assignment]
    return "_".join(parts)


def initial_assignments(split_variables: tuple[int, ...]) -> list[tuple[int, ...]]:
    return [
        tuple(variable if bit else -variable for variable, bit in zip(split_variables, bits))
        for bits in itertools.product((0, 1), repeat=len(split_variables))
    ]


def directory_bytes(root: Path) -> int:
    return sum(path.stat().st_size for path in root.rglob("*") if path.is_file())


def parse_lrat_metrics(path: Path, base_clauses: int) -> dict[str, int | bool]:
    additions = 0
    hint_edges = 0
    expected_id = base_clauses + 1
    ended = False
    with path.open("r", encoding="ascii") as stream:
        for line_number, raw in enumerate(stream, start=1):
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if ended:
                raise ValueError(f"{path}:{line_number}: addition after empty clause")
            fields = [int(field) for field in line.split()]
            if not fields or fields[0] != expected_id:
                raise ValueError(f"{path}:{line_number}: non-dense LRAT clause id")
            try:
                clause_end = fields.index(0, 1)
                hints_end = fields.index(0, clause_end + 1)
            except ValueError as error:
                raise ValueError(f"{path}:{line_number}: malformed LRAT row") from error
            if hints_end != len(fields) - 1:
                raise ValueError(f"{path}:{line_number}: LRAT deletion tail is not supported")
            hints = fields[clause_end + 1:hints_end]
            if any(hint <= 0 or hint >= expected_id for hint in hints):
                raise ValueError(f"{path}:{line_number}: invalid positive hint")
            additions += 1
            hint_edges += len(hints)
            ended = clause_end == 1
            expected_id += 1
    if not ended:
        raise ValueError(f"{path}: proof does not end in an empty clause")
    return {
        "additions": additions,
        "hint_edges": hint_edges,
        "ends_in_empty_clause": ended,
        "bytes": path.stat().st_size,
    }


def child_limits() -> None:
    resource.setrlimit(resource.RLIMIT_AS, (PROCESS_MEMORY_BYTES, PROCESS_MEMORY_BYTES))
    resource.setrlimit(resource.RLIMIT_CPU, (PROCESS_SECONDS, PROCESS_SECONDS))


def run_command(command: list[str], log_prefix: Path, accepted_codes: set[int]) -> dict[str, object]:
    start = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    try:
        completed = subprocess.run(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
            timeout=PROCESS_SECONDS,
            preexec_fn=child_limits,
        )
        timed_out = False
    except subprocess.TimeoutExpired as error:
        completed = None
        timed_out = True
        stdout = error.stdout or ""
        stderr = error.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", errors="replace")
        log_prefix.with_suffix(".stdout.log").write_text(stdout, encoding="utf-8")
        log_prefix.with_suffix(".stderr.log").write_text(stderr, encoding="utf-8")
    elapsed = time.monotonic() - start
    after = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    if completed is not None:
        log_prefix.with_suffix(".stdout.log").write_text(completed.stdout, encoding="utf-8")
        log_prefix.with_suffix(".stderr.log").write_text(completed.stderr, encoding="utf-8")
        return_code = completed.returncode
    else:
        return_code = None
    result = {
        "command": command,
        "elapsed_seconds": round(elapsed, 3),
        "return_code": return_code,
        "timed_out": timed_out,
        "observed_children_ru_maxrss_kib": max(before, after),
        "accepted": not timed_out and return_code in accepted_codes,
    }
    if not result["accepted"]:
        raise RuntimeError(f"command failed under frozen gate: {json.dumps(result, sort_keys=True)}")
    return result


def prepare(source_cnf: Path, output: Path, split_variables: tuple[int, ...]) -> dict[str, object]:
    if sha256(source_cnf) != EXPECTED_SOURCE_SHA256:
        raise ValueError("frozen Fin11 core CNF SHA-256 mismatch")
    variables, clauses = parse_cnf(source_cnf)
    if (variables, len(clauses)) != (EXPECTED_SOURCE_VARIABLES, EXPECTED_SOURCE_CLAUSES):
        raise ValueError("frozen Fin11 core CNF dimensions mismatch")
    if len(set(split_variables)) != len(split_variables):
        raise ValueError("cube split variables must be distinct")
    if any(variable <= 0 or variable > variables for variable in split_variables):
        raise ValueError("cube split variable is out of range")

    output.mkdir(parents=True, exist_ok=True)
    branches: list[dict[str, object]] = []
    for assignment in initial_assignments(split_variables):
        name = branch_name(assignment)
        branch_dir = output / name
        branch_dir.mkdir(parents=True, exist_ok=True)
        child_cnf = branch_dir / "child.cnf"
        units = [(literal,) for literal in assignment]
        write_cnf(child_cnf, variables, [*clauses, *units])
        branches.append(
            {
                "name": name,
                "assignment": {str(abs(literal)): literal > 0 for literal in assignment},
                "unit_literals": list(assignment),
                "cnf": str(child_cnf.relative_to(output)),
                "cnf_sha256": sha256(child_cnf),
                "variables": variables,
                "base_clauses": len(clauses) + len(units),
                "status": "prepared",
            }
        )

    manifest: dict[str, object] = {
        "schema_version": 1,
        "model": "frozen Fin11 synchronized-five-fan causal core plus exhaustive units",
        "source": {
            "path": str(source_cnf),
            "sha256": EXPECTED_SOURCE_SHA256,
            "variables": variables,
            "clauses": len(clauses),
        },
        "split": {
            "depth": len(split_variables),
            "variables": list(split_variables),
            "branch_count": 2 ** len(split_variables),
            "semantics": "positive unit means true; negative unit means false",
        },
        "thresholds": {
            "process_seconds": PROCESS_SECONDS,
            "process_memory_bytes": PROCESS_MEMORY_BYTES,
            "total_output_bytes": OUTPUT_BYTES,
            "initial_combined_bytes": INITIAL_COMBINED_BYTES,
            "initial_max_additions": INITIAL_MAX_ADDITIONS,
            "initial_max_hint_edges": INITIAL_MAX_HINT_EDGES,
            "final_max_additions": FINAL_MAX_ADDITIONS,
            "final_max_hint_edges": FINAL_MAX_HINT_EDGES,
            "final_max_base_clauses": FINAL_MAX_BASE_CLAUSES,
            "final_max_lrat_bytes": FINAL_MAX_LRAT_BYTES,
        },
        "branches": branches,
        "status": "prepared",
    }
    manifest_path = output / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return manifest


def certify(
    source_cnf: Path,
    output: Path,
    budget_root: Path,
    solver: Path,
    translator: Path,
    checker: Path,
    extractor: Path,
    seed: int,
    prune_full_proofs: bool,
) -> dict[str, object]:
    manifest_path = output / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    commands: list[dict[str, object]] = list(manifest.get("commands", []))
    for branch in manifest["branches"]:
        branch_dir = output / branch["name"]
        child_cnf = output / branch["cnf"]
        proof_rup = branch_dir / "proof.rup"
        proof_lrat = branch_dir / "proof.lrat"
        core_dir = branch_dir / "core"
        if branch.get("status") == "certified":
            if prune_full_proofs:
                proof_rup.unlink(missing_ok=True)
                proof_lrat.unlink(missing_ok=True)
                branch["proof"]["full_artifacts_pruned"] = True
            continue
        commands.append(
            run_command(
                [str(solver), str(child_cnf), str(seed), str(proof_rup)],
                branch_dir / "solver",
                {20},
            )
        )
        commands.append(
            run_command(
                [str(translator), str(child_cnf), str(proof_rup), str(proof_lrat)],
                branch_dir / "translator",
                {0},
            )
        )
        commands.append(
            run_command(
                [str(checker), str(child_cnf), str(proof_lrat)],
                branch_dir / "full-checker",
                {0},
            )
        )
        commands.append(
            run_command(
                [sys.executable, str(extractor), str(child_cnf), str(proof_lrat), str(core_dir)],
                branch_dir / "extractor",
                {0},
            )
        )
        commands.append(
            run_command(
                [str(checker), str(core_dir / "core.cnf"), str(core_dir / "core.lrat")],
                branch_dir / "core-checker",
                {0},
            )
        )
        core_map = json.loads((core_dir / "core-map.json").read_text())
        core = core_map["core"]
        lrat_metrics = parse_lrat_metrics(core_dir / "core.lrat", core["base_clauses"])
        branch["proof"] = {
            "rup": str(proof_rup.relative_to(output)),
            "rup_sha256": sha256(proof_rup),
            "lrat": str(proof_lrat.relative_to(output)),
            "lrat_sha256": sha256(proof_lrat),
            "core_cnf": str((core_dir / "core.cnf").relative_to(output)),
            "core_cnf_sha256": sha256(core_dir / "core.cnf"),
            "core_lrat": str((core_dir / "core.lrat").relative_to(output)),
            "core_lrat_sha256": sha256(core_dir / "core.lrat"),
            "core_map": str((core_dir / "core-map.json").relative_to(output)),
            "core_map_sha256": sha256(core_dir / "core-map.json"),
            "core_variables": core["variables"],
            "core_base_clauses": core["base_clauses"],
            **lrat_metrics,
        }
        branch["final_leaf_target"] = {
            "met": (
                lrat_metrics["additions"] <= FINAL_MAX_ADDITIONS
                and lrat_metrics["hint_edges"] <= FINAL_MAX_HINT_EDGES
                and core["base_clauses"] <= FINAL_MAX_BASE_CLAUSES
                and lrat_metrics["bytes"] <= FINAL_MAX_LRAT_BYTES
            )
        }
        branch["status"] = "certified"
        if prune_full_proofs:
            proof_rup.unlink()
            proof_lrat.unlink()
            branch["proof"]["full_artifacts_pruned"] = True
        manifest["commands"] = commands
        manifest["output_bytes"] = directory_bytes(output)
        manifest["total_output_bytes"] = directory_bytes(budget_root)
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        if manifest["total_output_bytes"] > OUTPUT_BYTES:
            raise RuntimeError("Fin11 cube artifacts exceeded the 5 GiB frozen cap")

    proofs = [branch["proof"] for branch in manifest["branches"]]
    combined_bytes = directory_bytes(output)
    manifest["initial_gate"] = {
        "all_branches_certified": len(proofs) == len(manifest["branches"]),
        "worst_additions": max(proof["additions"] for proof in proofs),
        "worst_hint_edges": max(proof["hint_edges"] for proof in proofs),
        "combined_bytes": combined_bytes,
    }
    gate = manifest["initial_gate"]
    artifact_gate = (
        combined_bytes <= INITIAL_COMBINED_BYTES
        if manifest["split"]["depth"] == 2
        else directory_bytes(budget_root) <= OUTPUT_BYTES
    )
    gate["advance"] = (
        gate["all_branches_certified"]
        and gate["worst_additions"] <= INITIAL_MAX_ADDITIONS
        and gate["worst_hint_edges"] <= INITIAL_MAX_HINT_EDGES
        and artifact_gate
    )
    largest = max(
        manifest["branches"],
        key=lambda branch: (
            branch["proof"]["additions"],
            branch["proof"]["hint_edges"],
            branch["proof"]["bytes"],
        ),
    )
    manifest["largest_leaf"] = largest["name"]
    manifest["tools"] = {
        "solver": {"path": str(solver), "sha256": sha256(solver)},
        "translator": {"path": str(translator), "sha256": sha256(translator)},
        "checker": {"path": str(checker), "sha256": sha256(checker)},
        "extractor": {"path": str(extractor), "sha256": sha256(extractor)},
    }
    manifest["commands"] = commands
    manifest["output_bytes"] = combined_bytes
    manifest["total_output_bytes"] = directory_bytes(budget_root)
    manifest["status"] = "initial-gate-complete"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cnf",
        type=Path,
        default=Path("runs/agents/20260812-frontier-cycle/fin11/core/core.cnf"),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("runs/agents/20260812-promotion-wave/fin11-cubes"),
    )
    parser.add_argument("--budget-root", type=Path)
    parser.add_argument("--split-variable", type=int, action="append")
    parser.add_argument("--alternate-pair", action="store_true")
    parser.add_argument("--run-proofs", action="store_true")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--prune-full-proofs", action="store_true")
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--translator", type=Path)
    parser.add_argument("--checker", type=Path)
    parser.add_argument("--extractor", type=Path)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    if args.alternate_pair and args.split_variable:
        raise ValueError("--alternate-pair and --split-variable are mutually exclusive")
    if args.alternate_pair:
        split_variables = ALTERNATE_SPLIT_VARIABLES
    else:
        split_variables = tuple(args.split_variable or INITIAL_SPLIT_VARIABLES)
    allowed_splits = (INITIAL_SPLIT_VARIABLES, ALTERNATE_SPLIT_VARIABLES, *RECURSIVE_SPLIT_VARIABLES)
    if split_variables not in allowed_splits:
        raise ValueError("split variables do not match a frozen Fin11 cube depth")
    source_cnf = args.cnf.resolve()
    output = args.output.resolve()
    budget_root = args.budget_root.resolve() if args.budget_root else output
    if args.resume:
        manifest_path = output / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        if tuple(manifest["split"]["variables"]) != split_variables:
            raise ValueError("resume manifest split does not match the requested frozen depth")
        if manifest["source"]["sha256"] != EXPECTED_SOURCE_SHA256:
            raise ValueError("resume manifest source hash mismatch")
    else:
        manifest = prepare(source_cnf, output, split_variables)
    if args.run_proofs:
        tools = (args.solver, args.translator, args.checker, args.extractor)
        if any(tool is None for tool in tools):
            raise ValueError("--run-proofs requires --solver, --translator, --checker, and --extractor")
        manifest = certify(
            source_cnf,
            output,
            budget_root,
            args.solver.resolve(),
            args.translator.resolve(),
            args.checker.resolve(),
            args.extractor.resolve(),
            args.seed,
            args.prune_full_proofs,
        )
    print(json.dumps({"status": manifest["status"], "output": str(output)}, sort_keys=True))


if __name__ == "__main__":
    main()
