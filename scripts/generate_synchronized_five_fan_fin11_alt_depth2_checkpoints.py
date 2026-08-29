#!/usr/bin/env python3
"""Render the two frozen alternate-depth-two LRAT checkpoint branches.

This renderer has exactly two representations: the ordinary dependency-import
layout and the predeclared 16-segment prefix-aggregate layout.  It authenticates
all eight frozen artifacts before creating a staging directory.  It never
solves, rewrites, or replays a certificate; the ordered LRAT segment bytes
concatenate to the authenticated input LRAT byte-for-byte.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import tempfile


SEGMENT_COUNT = 256
BUNDLE_SIZE = 256
PREFIX_AGGREGATE_SIZE = 16
FINITE_MAX_HEARTBEATS = 1_000_000_000
MAX_IMPORTED_CLAUSES = 2_048
MAX_CARRY_INPUT_BYTES = 163_840
MAX_ADDITIONS_PER_SEGMENT = 1_000
MAX_LEAN_COLUMNS = 100
MAX_RENDER_BYTES = 2 * 1024 * 1024 * 1024
MODES = ("ordinary", "prefix-aggregate")
FORBIDDEN_LEAN_WORDS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
)
STAGING_RELATIVE = Path(
    "runs/agents/20260820-fin11-all-cubes-execution/checkpoint-renderer/staging"
)


@dataclass(frozen=True)
class ArtifactSpec:
    kind: str
    relative_path: str
    size: int
    sha256: str


@dataclass(frozen=True)
class BranchSpec:
    key: str
    side_label: str
    stem: str
    raw_declaration: str
    units: tuple[int, int]
    core_variables: int
    original_clauses: int
    learned_additions: int
    hint_edges: int
    minimum_additions_per_segment: int
    maximum_additions_per_segment: int
    maximum_crossing_width: int
    maximum_crossing_after_segment: int
    unique_exported_clauses: int
    final_empty_id: int
    peak_imported_clauses: int
    peak_import_segment: int
    peak_carry_input_bytes: int
    peak_carry_input_segment: int
    total_carry_input_bytes: int
    artifacts: tuple[ArtifactSpec, ...]

    @property
    def checkpoint_prefix(self) -> str:
        return f"{self.stem}Checkpoint"

    def artifact(self, kind: str) -> ArtifactSpec:
        matches = [artifact for artifact in self.artifacts if artifact.kind == kind]
        if len(matches) != 1:
            raise ValueError(f"expected exactly one {kind} artifact for {self.key}")
        return matches[0]


RIGHT_LEFT = BranchSpec(
    key="v015-0_v111-1",
    side_label="RightLeft",
    stem="SynchronizedFiveFanFin11AltDepth2RightLeft",
    raw_declaration=(
        "synchronizedFiveFanFin11_"
        "SynchronizedFiveFanFin11AltDepth2RightLeft_lrat_unsat"
    ),
    units=(-15, 111),
    core_variables=1880,
    original_clauses=14816,
    learned_additions=126630,
    hint_edges=4397627,
    minimum_additions_per_segment=348,
    maximum_additions_per_segment=912,
    maximum_crossing_width=12866,
    maximum_crossing_after_segment=137,
    unique_exported_clauses=33198,
    final_empty_id=141446,
    peak_imported_clauses=1763,
    peak_import_segment=239,
    peak_carry_input_bytes=145159,
    peak_carry_input_segment=239,
    total_carry_input_bytes=20614425,
    artifacts=(
        ArtifactSpec(
            "child_cnf",
            "runs/agents/20260812-promotion-wave/fin11-cubes/"
            "alternate-015-111/v015-0_v111-1/child.cnf",
            688280,
            "08131822ab2150e0fb764d794bd345d4b0a4f786d07a942bf49f7e9e277e1ae0",
        ),
        ArtifactSpec(
            "core_cnf",
            "runs/agents/20260812-promotion-wave/fin11-cubes/"
            "alternate-015-111/v015-0_v111-1/core/core.cnf",
            504981,
            "91413958440c383c8c2f3c75795db9c4935eb6a537786fe0a1ae805c8974084e",
        ),
        ArtifactSpec(
            "core_lrat",
            "runs/agents/20260812-promotion-wave/fin11-cubes/"
            "alternate-015-111/v015-0_v111-1/core/core.lrat",
            64262475,
            "041d1d9d71c41b810636bd9fc1a0db320f16b873acce6c213a27bf38a444ee73",
        ),
        ArtifactSpec(
            "core_map",
            "runs/agents/20260812-promotion-wave/fin11-cubes/"
            "alternate-015-111/v015-0_v111-1/core/core-map.json",
            1633146,
            "83cfe254a7935d12eb016d9b98e80701176100cb272fe73361bdd216dd57699e",
        ),
    ),
)

LEFT_LEFT = BranchSpec(
    key="v015-1_v111-1",
    side_label="LeftLeft",
    stem="SynchronizedFiveFanFin11AltDepth2LeftLeft",
    raw_declaration=(
        "synchronizedFiveFanFin11_"
        "SynchronizedFiveFanFin11AltDepth2LeftLeft_lrat_unsat"
    ),
    units=(15, 111),
    core_variables=1881,
    original_clauses=14911,
    learned_additions=126773,
    hint_edges=4311453,
    minimum_additions_per_segment=373,
    maximum_additions_per_segment=814,
    maximum_crossing_width=12926,
    maximum_crossing_after_segment=152,
    unique_exported_clauses=34991,
    final_empty_id=141684,
    peak_imported_clauses=1736,
    peak_import_segment=198,
    peak_carry_input_bytes=141110,
    peak_carry_input_segment=243,
    total_carry_input_bytes=21557686,
    artifacts=(
        ArtifactSpec(
            "child_cnf",
            "runs/agents/20260812-promotion-wave/fin11-cubes/"
            "alternate-015-111/v015-1_v111-1/child.cnf",
            688279,
            "a16ee4abb6a6c85417c2c44583492b981d3e2920a83561e1fdf18d88a034481b",
        ),
        ArtifactSpec(
            "core_cnf",
            "runs/agents/20260812-promotion-wave/fin11-cubes/"
            "alternate-015-111/v015-1_v111-1/core/core.cnf",
            512486,
            "876f979c837db789d9f2189a0a4d78efe3271e4f1a6416cbe48a4e759530960a",
        ),
        ArtifactSpec(
            "core_lrat",
            "runs/agents/20260812-promotion-wave/fin11-cubes/"
            "alternate-015-111/v015-1_v111-1/core/core.lrat",
            63652570,
            "0e27c0acc9d700acbc9ef69dfd6769f1f1263d3e392d38814a8b55d21968eeee",
        ),
        ArtifactSpec(
            "core_map",
            "runs/agents/20260812-promotion-wave/fin11-cubes/"
            "alternate-015-111/v015-1_v111-1/core/core-map.json",
            1635532,
            "8d3f050da30c3509983ad71d8585bf03ba8986367df835c9287985d236441768",
        ),
    ),
)

BRANCHES = (RIGHT_LEFT, LEFT_LEFT)
BRANCH_BY_KEY = {branch.key: branch for branch in BRANCHES}


@dataclass
class ProofAnalysis:
    size: int
    introduced: dict[int, int]
    imported_by_segment: list[set[int]]
    exported_by_segment: list[set[int]]
    additions_by_segment: list[int]
    deletions_by_segment: list[int]
    hint_edges: int
    final_empty_id: int
    final_empty_segment: int
    crossing_width_by_segment: list[int]


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def segment_at(offset: int, size: int) -> int:
    if size <= 0:
        raise ValueError("LRAT input must not be empty")
    return min(SEGMENT_COUNT - 1, offset * SEGMENT_COUNT // size)


def parse_addition(
    raw: bytes, offset: int
) -> tuple[int, list[bytes], list[int]] | None:
    fields = raw.split()
    if not fields:
        return None
    if len(fields) >= 2 and fields[1] == b"d":
        return None
    try:
        first_zero = fields.index(b"0", 1)
        second_zero = fields.index(b"0", first_zero + 1)
    except ValueError as exc:
        raise ValueError(f"unterminated LRAT addition at byte {offset}") from exc
    if second_zero != len(fields) - 1:
        raise ValueError(f"unexpected trailing LRAT fields at byte {offset}")
    clause_id = int(fields[0])
    literals = fields[1:first_zero]
    references = [int(token) for token in fields[first_zero + 1 : second_zero]]
    return clause_id, literals, references


def authenticate_artifact(repo_root: Path, artifact: ArtifactSpec) -> Path:
    path = repo_root / artifact.relative_path
    if not path.is_file():
        raise ValueError(f"missing frozen artifact: {artifact.relative_path}")
    if path.stat().st_size != artifact.size:
        raise ValueError(f"artifact byte mismatch: {artifact.relative_path}")
    if sha256_path(path) != artifact.sha256:
        raise ValueError(f"artifact SHA-256 mismatch: {artifact.relative_path}")
    return path


def authenticate_branch(repo_root: Path, branch: BranchSpec) -> dict[str, Path]:
    authenticated: dict[str, Path] = {}
    for artifact in branch.artifacts:
        authenticated[artifact.kind] = authenticate_artifact(repo_root, artifact)
    if set(authenticated) != {"child_cnf", "core_cnf", "core_lrat", "core_map"}:
        raise ValueError(f"artifact quartet mismatch for {branch.key}")
    return authenticated


def read_dimacs_summary(path: Path) -> tuple[int, int, tuple[int, ...]]:
    variables: int | None = None
    declared_clauses: int | None = None
    clauses = 0
    pending: list[int] = []
    units: list[int] = []
    with path.open("rb") as source:
        for line_number, raw in enumerate(source, start=1):
            stripped = raw.strip()
            if not stripped or stripped.startswith(b"c"):
                continue
            if stripped.startswith(b"p"):
                fields = stripped.split()
                if fields[:2] != [b"p", b"cnf"] or len(fields) != 4:
                    raise ValueError(f"invalid DIMACS header at line {line_number}")
                if variables is not None:
                    raise ValueError("duplicate DIMACS header")
                variables = int(fields[2])
                declared_clauses = int(fields[3])
                continue
            if variables is None:
                raise ValueError("DIMACS clause appears before its header")
            for field in stripped.split():
                literal = int(field)
                if literal == 0:
                    clauses += 1
                    if len(pending) == 1:
                        units.append(pending[0])
                    pending = []
                else:
                    pending.append(literal)
    if variables is None or declared_clauses is None:
        raise ValueError("missing DIMACS header")
    if pending:
        raise ValueError("unterminated DIMACS clause")
    if clauses != declared_clauses:
        raise ValueError(
            f"DIMACS clause count mismatch: header {declared_clauses}, rows {clauses}"
        )
    return variables, clauses, tuple(units)


def validate_core_cnf(path: Path, branch: BranchSpec) -> None:
    variables, clauses, units = read_dimacs_summary(path)
    if variables != branch.core_variables:
        raise ValueError(f"core variable count mismatch for {branch.key}")
    if clauses != branch.original_clauses:
        raise ValueError(f"core clause count mismatch for {branch.key}")
    if units != branch.units:
        raise ValueError(f"core branch units mismatch for {branch.key}: {units}")


def analyze_lrat(path: Path, branch: BranchSpec) -> ProofAnalysis:
    size = path.stat().st_size
    introduced: dict[int, int] = {}
    last_reference: dict[int, int] = {}
    imported_by_segment = [set() for _ in range(SEGMENT_COUNT)]
    additions = [0] * SEGMENT_COUNT
    deletions = [0] * SEGMENT_COUNT
    empty_clauses: list[tuple[int, int]] = []
    hint_edges = 0
    last_addition_id: int | None = None

    with path.open("rb") as source:
        while True:
            offset = source.tell()
            raw = source.readline()
            if not raw:
                break
            segment = segment_at(offset, size)
            fields = raw.split()
            if len(fields) >= 2 and fields[1] == b"d":
                deletions[segment] += 1
                continue
            parsed = parse_addition(raw, offset)
            if parsed is None:
                continue
            clause_id, literals, references = parsed
            additions[segment] += 1
            hint_edges += len(references)
            if clause_id in introduced:
                raise ValueError(f"duplicate learned clause ID {clause_id}")
            if clause_id <= branch.original_clauses:
                raise ValueError(f"learned clause ID overlaps core: {clause_id}")
            introduced[clause_id] = segment
            last_addition_id = clause_id
            if not literals:
                empty_clauses.append((clause_id, segment))
            for reference in references:
                if reference < 0:
                    raise ValueError(f"negative LRAT reference in clause {clause_id}")
                if reference <= branch.original_clauses:
                    continue
                defining_segment = introduced.get(reference)
                if defining_segment is None:
                    raise ValueError(
                        f"clause {clause_id} references unknown clause {reference}"
                    )
                last_reference[reference] = segment
                if defining_segment < segment:
                    imported_by_segment[segment].add(reference)

    if sum(deletions) != 0:
        raise ValueError(f"LRAT deletions are forbidden for {branch.key}")
    if len(empty_clauses) != 1:
        raise ValueError(f"expected exactly one empty LRAT clause for {branch.key}")
    final_empty_id, final_empty_segment = empty_clauses[0]
    if final_empty_id != branch.final_empty_id:
        raise ValueError(f"final empty clause ID mismatch for {branch.key}")
    if final_empty_segment != SEGMENT_COUNT - 1:
        raise ValueError(f"final empty clause is not in segment 255 for {branch.key}")
    if last_addition_id != final_empty_id:
        raise ValueError(f"empty clause is not the final LRAT addition for {branch.key}")

    exported_by_segment = [set() for _ in range(SEGMENT_COUNT)]
    for clause_id, last_segment in last_reference.items():
        defining_segment = introduced[clause_id]
        if defining_segment < last_segment:
            exported_by_segment[defining_segment].add(clause_id)
    crossing_widths = []
    for segment in range(SEGMENT_COUNT - 1):
        width = sum(
            1
            for clause_id, last_segment in last_reference.items()
            if introduced[clause_id] <= segment < last_segment
        )
        crossing_widths.append(width)
    crossing_widths.append(0)
    analysis = ProofAnalysis(
        size=size,
        introduced=introduced,
        imported_by_segment=imported_by_segment,
        exported_by_segment=exported_by_segment,
        additions_by_segment=additions,
        deletions_by_segment=deletions,
        hint_edges=hint_edges,
        final_empty_id=final_empty_id,
        final_empty_segment=final_empty_segment,
        crossing_width_by_segment=crossing_widths,
    )
    validate_analysis(analysis, branch)
    return analysis


def unique_peak(values: list[int], expected_value: int, expected_index: int) -> None:
    if max(values) != expected_value:
        raise ValueError(f"peak mismatch: expected {expected_value}, got {max(values)}")
    if values.index(expected_value) != expected_index:
        raise ValueError(
            f"first peak index mismatch: expected {expected_index}, "
            f"got {values.index(expected_value)}"
        )


def validate_analysis(analysis: ProofAnalysis, branch: BranchSpec) -> None:
    if len(analysis.additions_by_segment) != SEGMENT_COUNT:
        raise ValueError("checkpoint segment count must be exactly 256")
    if sum(analysis.additions_by_segment) != branch.learned_additions:
        raise ValueError(f"learned-addition count mismatch for {branch.key}")
    if min(analysis.additions_by_segment) != branch.minimum_additions_per_segment:
        raise ValueError(f"minimum segment load mismatch for {branch.key}")
    if max(analysis.additions_by_segment) != branch.maximum_additions_per_segment:
        raise ValueError(f"maximum segment load mismatch for {branch.key}")
    if max(analysis.additions_by_segment) > MAX_ADDITIONS_PER_SEGMENT:
        raise ValueError("segment addition ceiling exceeded")
    if analysis.hint_edges != branch.hint_edges:
        raise ValueError(f"LRAT hint-edge mismatch for {branch.key}")
    if len(analysis.introduced) != branch.learned_additions:
        raise ValueError(f"unique learned-clause count mismatch for {branch.key}")
    exported = sum(len(values) for values in analysis.exported_by_segment)
    if exported != branch.unique_exported_clauses:
        raise ValueError(f"exported learned-clause count mismatch for {branch.key}")
    unique_peak(
        analysis.crossing_width_by_segment,
        branch.maximum_crossing_width,
        branch.maximum_crossing_after_segment,
    )
    imported_counts = [len(values) for values in analysis.imported_by_segment]
    unique_peak(
        imported_counts,
        branch.peak_imported_clauses,
        branch.peak_import_segment,
    )
    if max(imported_counts) > MAX_IMPORTED_CLAUSES:
        raise ValueError("imported learned-clause ceiling exceeded")
    if analysis.final_empty_id != branch.final_empty_id:
        raise ValueError("final empty clause ID mismatch")
    if analysis.final_empty_segment != SEGMENT_COUNT - 1:
        raise ValueError("final empty clause placement mismatch")


def validate_carry_input_bytes(values: list[int], branch: BranchSpec) -> None:
    if len(values) != SEGMENT_COUNT:
        raise ValueError("carry-input ledger must contain exactly 256 segments")
    unique_peak(
        values,
        branch.peak_carry_input_bytes,
        branch.peak_carry_input_segment,
    )
    if sum(values) != branch.total_carry_input_bytes:
        raise ValueError(f"total carry-input byte mismatch for {branch.key}")
    if max(values) > MAX_CARRY_INPUT_BYTES:
        raise ValueError("serialized carry-input ceiling exceeded")


def validate_render_envelope(total_bytes: int) -> None:
    if total_bytes < 0:
        raise ValueError("render byte count must be nonnegative")
    if total_bytes > MAX_RENDER_BYTES:
        raise ValueError("checkpoint render exceeds the frozen byte envelope")


def copy_authenticated(source: Path, target: Path, artifact: ArtifactSpec) -> None:
    target.parent.mkdir(parents=True, exist_ok=True)
    with source.open("rb") as input_file, target.open("xb") as output_file:
        shutil.copyfileobj(input_file, output_file, length=1024 * 1024)
    if target.stat().st_size != artifact.size or sha256_path(target) != artifact.sha256:
        raise ValueError(f"staged artifact copy mismatch: {artifact.kind}")


def write_checkpoint_data(
    lrat: Path,
    data_dir: Path,
    analysis: ProofAnalysis,
    branch: BranchSpec,
) -> dict[str, object]:
    segment_paths = [data_dir / f"segment-{i:03d}.lrat" for i in range(SEGMENT_COUNT)]
    outputs = [path.open("xb") for path in segment_paths]
    exported_literals: dict[int, bytes] = {}
    try:
        with lrat.open("rb") as source:
            while True:
                offset = source.tell()
                raw = source.readline()
                if not raw:
                    break
                segment = segment_at(offset, analysis.size)
                outputs[segment].write(raw)
                parsed = parse_addition(raw, offset)
                if parsed is None:
                    continue
                clause_id, literals, _ = parsed
                if clause_id in analysis.exported_by_segment[segment]:
                    exported_literals[clause_id] = b" ".join(literals)
    finally:
        for output in outputs:
            output.close()

    reconstructed = hashlib.sha256()
    for path in segment_paths:
        with path.open("rb") as source:
            for chunk in iter(lambda: source.read(1024 * 1024), b""):
                reconstructed.update(chunk)
    if reconstructed.hexdigest() != branch.artifact("core_lrat").sha256:
        raise ValueError("segmented LRAT does not reconstruct the frozen input bytes")

    ordered_exports = [sorted(values) for values in analysis.exported_by_segment]
    export_indices = [
        {clause_id: index for index, clause_id in enumerate(values)}
        for values in ordered_exports
    ]
    carry_input_paths: list[Path] = []
    carry_output_paths: list[Path] = []
    carry_input_bytes: list[int] = []
    for segment in range(SEGMENT_COUNT):
        input_path = data_dir / f"carry-input-{segment:03d}.txt"
        output_path = data_dir / f"carry-output-{segment:03d}.txt"
        with input_path.open("xb") as output:
            for clause_id in sorted(analysis.imported_by_segment[segment]):
                defining_segment = analysis.introduced[clause_id]
                export_index = export_indices[defining_segment][clause_id]
                bundle_number = export_index // BUNDLE_SIZE
                bundle_start = bundle_number * BUNDLE_SIZE
                actual_bundle_size = min(
                    BUNDLE_SIZE,
                    len(ordered_exports[defining_segment]) - bundle_start,
                )
                bundle_index = export_index - bundle_start
                literals = exported_literals[clause_id]
                prefix = (
                    f"{clause_id} {defining_segment} {bundle_number} "
                    f"{actual_bundle_size} {bundle_index} "
                ).encode()
                output.write(prefix + literals + b" 0\n")
        with output_path.open("x", encoding="utf-8") as output:
            for clause_id in ordered_exports[segment]:
                output.write(f"{clause_id}\n")
        carry_input_paths.append(input_path)
        carry_output_paths.append(output_path)
        carry_input_bytes.append(input_path.stat().st_size)

    validate_carry_input_bytes(carry_input_bytes, branch)
    return {
        "segment_paths": segment_paths,
        "carry_input_paths": carry_input_paths,
        "carry_output_paths": carry_output_paths,
        "carry_input_bytes": carry_input_bytes,
        "segment_sha256": [sha256_path(path) for path in segment_paths],
        "carry_input_sha256": [sha256_path(path) for path in carry_input_paths],
        "carry_output_sha256": [sha256_path(path) for path in carry_output_paths],
    }


def maximum_columns(source: str) -> int:
    return max((len(line) for line in source.splitlines()), default=0)


def validate_lean_source(source: str, require_heartbeat: bool = False) -> None:
    if not source.endswith("\n"):
        raise ValueError("generated Lean source must end in one newline")
    if any(line.endswith((" ", "\t")) for line in source.splitlines()):
        raise ValueError("generated Lean source has trailing whitespace")
    if maximum_columns(source) > MAX_LEAN_COLUMNS:
        raise ValueError("generated Lean source exceeds 100 columns")
    for word in FORBIDDEN_LEAN_WORDS:
        if re.search(rf"\b{re.escape(word)}\b", source):
            raise ValueError(f"forbidden Lean trust token: {word}")
    if "maxHeartbeats 0" in source:
        raise ValueError("unbounded maxHeartbeats is forbidden")
    if require_heartbeat:
        expected = f"set_option maxHeartbeats {FINITE_MAX_HEARTBEATS}"
        if expected not in source:
            raise ValueError("checkpoint segment lacks the frozen finite heartbeat cap")


def write_lean(path: Path, source: str, require_heartbeat: bool = False) -> None:
    validate_lean_source(source, require_heartbeat=require_heartbeat)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8", newline="\n")


def context_source(branch: BranchSpec, core_include: str) -> str:
    prefix = branch.checkpoint_prefix
    return f"""-- Generated checkpoint source; do not edit.
module

public import ErdosSzekeres.LRATCheckpoint

@[expose] public section

namespace ErdosSzekeres

-- Checkpoint projections are proof infrastructure, not useful premises.
run_cmd
  Lean.modifyEnv fun env =>
    Lean.LibrarySuggestions.nameDenyListExt.addEntry env
      "{prefix}"

lrat_checkpoint_context {prefix}Context
  (include_str "{core_include}")

end ErdosSzekeres

end
"""


def segment_source(
    branch: BranchSpec,
    segment: int,
    import_names: list[str],
    data_prefix: str,
) -> str:
    prefix = branch.checkpoint_prefix
    imports = "".join(f"import ErdosSzekeres.{name}\n" for name in import_names)
    final_import = (
        "public import ErdosSzekeres.LRATCheckpointFinal\n"
        if segment == SEGMENT_COUNT - 1
        else ""
    )
    command = (
        "lrat_checkpoint_final_segment"
        if segment == SEGMENT_COUNT - 1
        else "lrat_checkpoint_segment"
    )
    return f"""-- Generated checkpoint source; do not edit.
module

public import ErdosSzekeres.{prefix}Context
{final_import}{imports}
public section

namespace ErdosSzekeres

set_option maxHeartbeats {FINITE_MAX_HEARTBEATS}

{command}
  {prefix}Context
  {prefix} {segment} {BUNDLE_SIZE}
  (include_str "{data_prefix}/core.cnf")
  (include_str "{data_prefix}/segment-{segment:03d}.lrat")
  (include_str "{data_prefix}/carry-input-{segment:03d}.txt")
  (include_str "{data_prefix}/carry-output-{segment:03d}.txt")

end ErdosSzekeres

end
"""


def prefix_aggregate_name(branch: BranchSpec, endpoint: int) -> str:
    return f"{branch.checkpoint_prefix}PrefixAggregate{endpoint:03d}"


def aggregate_source(branch: BranchSpec, endpoint: int) -> str:
    if endpoint % PREFIX_AGGREGATE_SIZE != PREFIX_AGGREGATE_SIZE - 1:
        raise ValueError("prefix aggregate endpoint must close a 16-segment block")
    start = endpoint - PREFIX_AGGREGATE_SIZE + 1
    imports: list[str] = []
    if start:
        imports.append(prefix_aggregate_name(branch, start - 1))
    imports.extend(
        f"{branch.checkpoint_prefix}Segment{segment:03d}"
        for segment in range(start, endpoint + 1)
    )
    rendered = "".join(
        f"public import ErdosSzekeres.{module_name}\n" for module_name in imports
    )
    return f"""-- Generated checkpoint prefix aggregate; do not edit.
module

{rendered}
@[expose] public section

end
"""


def leaf_source(branch: BranchSpec, imported_module: str) -> str:
    prefix = branch.checkpoint_prefix
    return f"""-- Generated checkpoint leaf; do not edit.
module

public import ErdosSzekeres.{imported_module}

@[expose] public section

namespace ErdosSzekeres

run_cmd
  Lean.Elab.Command.liftTermElabM do
    let sourceName :=
      `ErdosSzekeres.{prefix}.publicUnsat
    let targetName :=
      `ErdosSzekeres.{branch.raw_declaration}
    let info ← Lean.getConstInfo sourceName
    Lean.withExporting do
      Lean.addDecl <| .thmDecl {{
        name := targetName
        levelParams := info.levelParams
        type := info.type
        value := Lean.mkConst sourceName (info.levelParams.map Lean.mkLevelParam)
      }}

end ErdosSzekeres

end
"""


def segment_import_names(
    branch: BranchSpec,
    segment: int,
    defining_segments: list[int],
    mode: str,
) -> list[str]:
    if mode == "ordinary":
        return [
            f"{branch.checkpoint_prefix}Segment{defining_segment:03d}"
            for defining_segment in defining_segments
        ]
    if mode != "prefix-aggregate":
        raise ValueError(f"unsupported checkpoint representation: {mode}")
    block_start = segment // PREFIX_AGGREGATE_SIZE * PREFIX_AGGREGATE_SIZE
    names: list[str] = []
    if block_start:
        names.append(prefix_aggregate_name(branch, block_start - 1))
    names.extend(
        f"{branch.checkpoint_prefix}Segment{defining_segment:03d}"
        for defining_segment in defining_segments
        if defining_segment >= block_start
    )
    return names


def render_lean_modules(
    lean_dir: Path,
    branch: BranchSpec,
    analysis: ProofAnalysis,
    mode: str,
) -> dict[str, object]:
    data_prefix = f"Fin11AltDepth2CheckpointData/{branch.side_label}"
    context_name = f"{branch.checkpoint_prefix}Context"
    write_lean(
        lean_dir / f"{context_name}.lean",
        context_source(branch, f"{data_prefix}/core.cnf"),
    )
    direct_imports: list[list[str]] = []
    for segment in range(SEGMENT_COUNT):
        defining_segments = sorted(
            {
                analysis.introduced[clause_id]
                for clause_id in analysis.imported_by_segment[segment]
            }
        )
        names = segment_import_names(branch, segment, defining_segments, mode)
        direct_imports.append(names)
        module_name = f"{branch.checkpoint_prefix}Segment{segment:03d}"
        write_lean(
            lean_dir / f"{module_name}.lean",
            segment_source(branch, segment, names, data_prefix),
            require_heartbeat=True,
        )

    aggregates: list[str] = []
    if mode == "prefix-aggregate":
        for endpoint in range(
            PREFIX_AGGREGATE_SIZE - 1,
            SEGMENT_COUNT,
            PREFIX_AGGREGATE_SIZE,
        ):
            module_name = prefix_aggregate_name(branch, endpoint)
            aggregates.append(module_name)
            write_lean(
                lean_dir / f"{module_name}.lean",
                aggregate_source(branch, endpoint),
            )
        leaf_import = aggregates[-1]
    else:
        leaf_import = f"{branch.checkpoint_prefix}Segment255"
    leaf_name = f"{branch.checkpoint_prefix}Leaf"
    write_lean(
        lean_dir / f"{leaf_name}.lean",
        leaf_source(branch, leaf_import),
    )
    return {
        "context_module": context_name,
        "segment_modules": SEGMENT_COUNT,
        "prefix_aggregate_modules": aggregates,
        "leaf_module": leaf_name,
        "leaf_import": leaf_import,
        "direct_imports_by_segment": direct_imports,
    }


def output_record(path: Path, root: Path) -> dict[str, object]:
    relative = path.relative_to(root).as_posix()
    if relative.startswith("/") or ".." in Path(relative).parts:
        raise ValueError(f"output ownership violation: {relative}")
    record: dict[str, object] = {
        "path": relative,
        "bytes": path.stat().st_size,
        "sha256": sha256_path(path),
    }
    if path.suffix == ".lean":
        source = path.read_text(encoding="utf-8")
        validate_lean_source(
            source,
            require_heartbeat="CheckpointSegment" in path.name,
        )
        record["lines"] = len(source.splitlines())
        record["maximum_columns"] = maximum_columns(source)
    return record


def manifest_text(manifest: dict[str, object]) -> str:
    return json.dumps(manifest, indent=2, sort_keys=True) + "\n"


def render_branch_to_new_root(
    repo_root: Path,
    branch_root: Path,
    branch: BranchSpec,
    mode: str,
) -> Path:
    if mode not in MODES:
        raise ValueError(f"unsupported checkpoint representation: {mode}")
    if branch not in BRANCHES:
        raise ValueError("only the two frozen primary branches are supported")
    if branch_root.exists():
        raise ValueError(f"refusing to overwrite staging output: {branch_root}")

    paths = authenticate_branch(repo_root, branch)
    validate_core_cnf(paths["core_cnf"], branch)
    analysis = analyze_lrat(paths["core_lrat"], branch)

    lean_dir = branch_root / "lean" / "ErdosSzekeres"
    data_dir = (
        lean_dir / "Fin11AltDepth2CheckpointData" / branch.side_label
    )
    data_dir.mkdir(parents=True)
    copy_authenticated(
        paths["child_cnf"],
        data_dir / "child.cnf",
        branch.artifact("child_cnf"),
    )
    copy_authenticated(
        paths["core_cnf"],
        data_dir / "core.cnf",
        branch.artifact("core_cnf"),
    )
    copy_authenticated(
        paths["core_map"],
        data_dir / "core-map.json",
        branch.artifact("core_map"),
    )
    checkpoint_data = write_checkpoint_data(
        paths["core_lrat"], data_dir, analysis, branch
    )
    module_metadata = render_lean_modules(
        lean_dir, branch, analysis, mode
    )

    output_paths = sorted(
        path for path in branch_root.rglob("*") if path.is_file()
    )
    output_records = [output_record(path, branch_root) for path in output_paths]
    total_bytes = sum(int(record["bytes"]) for record in output_records)
    validate_render_envelope(total_bytes)
    artifact_ledger = [
        {
            "kind": artifact.kind,
            "path": artifact.relative_path,
            "bytes": artifact.size,
            "sha256": artifact.sha256,
        }
        for artifact in branch.artifacts
    ]
    manifest: dict[str, object] = {
        "schema_version": 1,
        "branch": branch.key,
        "branch_units": list(branch.units),
        "stem": branch.stem,
        "checkpoint_prefix": branch.checkpoint_prefix,
        "raw_lrat_declaration": branch.raw_declaration,
        "representation": mode,
        "artifact_ledger": artifact_ledger,
        "segments": SEGMENT_COUNT,
        "bundle_size": BUNDLE_SIZE,
        "finite_maxHeartbeats": FINITE_MAX_HEARTBEATS,
        "original_clauses": branch.original_clauses,
        "learned_additions": len(analysis.introduced),
        "hint_edges": analysis.hint_edges,
        "final_empty_id": analysis.final_empty_id,
        "final_empty_segment": analysis.final_empty_segment,
        "additions_by_segment": analysis.additions_by_segment,
        "imports_by_segment": [
            len(values) for values in analysis.imported_by_segment
        ],
        "exports_by_segment": [
            len(values) for values in analysis.exported_by_segment
        ],
        "crossing_width_by_segment": analysis.crossing_width_by_segment,
        "carry_input_bytes": checkpoint_data["carry_input_bytes"],
        "segment_sha256": checkpoint_data["segment_sha256"],
        "carry_input_sha256": checkpoint_data["carry_input_sha256"],
        "carry_output_sha256": checkpoint_data["carry_output_sha256"],
        "reconstructed_lrat_sha256": branch.artifact("core_lrat").sha256,
        "module_metadata": module_metadata,
        "limits": {
            "maximum_imported_clauses": MAX_IMPORTED_CLAUSES,
            "maximum_carry_input_bytes": MAX_CARRY_INPUT_BYTES,
            "maximum_additions_per_segment": MAX_ADDITIONS_PER_SEGMENT,
            "maximum_lean_columns": MAX_LEAN_COLUMNS,
            "maximum_render_bytes": MAX_RENDER_BYTES,
        },
        "output_bytes_before_manifest": total_bytes,
        "outputs": output_records,
    }
    manifest_path = branch_root / "manifest.json"
    manifest_path.write_text(manifest_text(manifest), encoding="utf-8", newline="\n")
    validate_render_envelope(
        sum(path.stat().st_size for path in branch_root.rglob("*") if path.is_file())
    )
    return manifest_path


def repo_root_from_script() -> Path:
    return Path(__file__).resolve().parents[1]


def owned_branch_root(repo_root: Path, branch: BranchSpec, mode: str) -> Path:
    if mode not in MODES:
        raise ValueError(f"unsupported checkpoint representation: {mode}")
    repository = repo_root.resolve()
    root = (repository / STAGING_RELATIVE / mode / branch.key).resolve()
    owner = (repository / STAGING_RELATIVE).resolve()
    if owner == repository or repository not in owner.parents:
        raise ValueError("checkpoint staging path escapes repository ownership")
    if root == owner or owner not in root.parents:
        raise ValueError("checkpoint staging path escapes packet ownership")
    return root


def render_owned_branch(repo_root: Path, branch: BranchSpec, mode: str) -> Path:
    final_root = owned_branch_root(repo_root, branch, mode)
    if final_root.exists():
        raise ValueError(f"refusing to overwrite staging output: {final_root}")
    final_root.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(
        tempfile.mkdtemp(prefix=f".{branch.key}.", dir=final_root.parent)
    )
    temporary.rmdir()
    try:
        manifest = render_branch_to_new_root(repo_root, temporary, branch, mode)
        os.replace(temporary, final_root)
        return final_root / manifest.name
    except BaseException:
        shutil.rmtree(temporary, ignore_errors=True)
        raise


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--branch", choices=tuple(BRANCH_BY_KEY), required=True)
    parser.add_argument("--mode", choices=MODES, default="ordinary")
    args = parser.parse_args()
    repo_root = repo_root_from_script()
    manifest = render_owned_branch(repo_root, BRANCH_BY_KEY[args.branch], args.mode)
    print(manifest.relative_to(repo_root).as_posix())


if __name__ == "__main__":
    main()
