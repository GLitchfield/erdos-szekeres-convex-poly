#!/usr/bin/env python3
"""Source-only corruption tests for the frozen Fin11 shallow renderer."""

from __future__ import annotations

from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import re
import runpy


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "scripts/generate_synchronized_five_fan_fin11_alt_depth2_semantic.py"
CONTROL = ROOT / "scripts/generate_synchronized_five_fan_fin11_semantic.py"
EXPECTED_CONTROL_SHA256 = (
    "32d0687ebb7fb4411afaf0fc496da9fe780694a89de11fb6dc776df390ad05d2"
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def expect_failure(label: str, action: object) -> None:
    try:
        action()
    except (AssertionError, KeyError, TypeError, ValueError):
        return
    raise AssertionError(f"corruption survived: {label}")


def clone_source(source: dict[str, object]) -> dict[str, object]:
    result = copy.deepcopy({
        key: value for key, value in source.items() if key != "control"
    })
    result["control"] = source["control"]
    return result


def semantic_declarations(
    generator: dict[str, object], outputs: dict[Path, bytes]
) -> set[str]:
    declarations = set()
    pattern = re.compile(
        r"^theorem "
        r"(synchronizedFiveFanFin11AltDepth2Semantic_clause[0-9]{5})",
        re.MULTILINE,
    )
    for relative, data in outputs.items():
        if relative.parts[0] == "ErdosSzekeres":
            declarations.update(pattern.findall(data.decode()))
    return declarations


def assert_exact_clause_coverage(
    source: dict[str, object], outputs: dict[Path, bytes]
) -> None:
    expected = {
        f"synchronizedFiveFanFin11AltDepth2Semantic_clause{item:05d}"
        for item in source["union_ids"]
    }
    actual = semantic_declarations({}, outputs)
    require(actual == expected, "semantic theorem set is not the exact union")


def assert_branch_consumers(
    generator: dict[str, object],
    source: dict[str, object],
    outputs: dict[Path, bytes],
) -> None:
    prefix = "ErdosSzekeres/"
    reference = re.compile(
        r"exact synchronizedFiveFanFin11AltDepth2Semantic_clause([0-9]{5}) chi"
    )
    atom_argument = re.compile(
        r"^      \(SynchronizedFiveFanFin11OriginalAtom([0-9]{4}) chi\)$",
        re.MULTILINE,
    )
    for branch in generator["BRANCH_ORDER"]:
        spec = generator["BRANCHES"][branch]
        relative = Path(prefix + spec["consumer"] + ".lean")
        text = outputs[relative].decode()
        expected_ids = Counter(
            int(entry["semantic_id"])
            for entry in source["branches"][branch]["entries"]
        )
        actual_ids = Counter(map(int, reference.findall(text)))
        require(actual_ids == expected_ids, f"{branch}: branch obligation mismatch")
        expected_atoms = [
            source["branches"][branch]["new_to_old"][dense]
            for dense in range(1, spec["variables"] + 1)
        ]
        actual_atoms = list(map(int, atom_argument.findall(text)))
        require(actual_atoms == expected_atoms, f"{branch}: dense argument map changed")
        require(text.count("hunit_") >= 4, f"{branch}: unit adapter missing")
        require("maxHeartbeats" not in text, f"{branch}: heartbeat escape present")
        public_interface = (
            "public import "
            "ErdosSzekeres.SynchronizedFiveFanFin11BranchInterface"
        )
        require(
            text.count("public import") == 1 and public_interface in text,
            f"{branch}: public branch interface import mismatch",
        )
    negative = outputs[
        Path(prefix + generator["BRANCHES"][generator["BRANCH_ORDER"][0]][
            "consumer"
        ] + ".lean")
    ].decode()
    require(
        961 not in map(int, atom_argument.findall(negative)),
        "negative branch unexpectedly includes dropped atom 961",
    )


def assert_module_partition(
    generator: dict[str, object], outputs: dict[Path, bytes]
) -> None:
    project = sorted(
        relative for relative in outputs
        if relative.parts[0] == "ErdosSzekeres" and relative.suffix == ".lean"
    )
    require(len(project) == 383, "project module count changed")
    counts = Counter()
    for relative in project:
        name = relative.name
        if "AtomSegment" in name:
            counts["atom_segment"] += 1
        elif "AtomBundle" in name:
            counts["atom_bundle"] += 1
        elif "SupportSegment" in name:
            counts["support_segment"] += 1
        elif "SupportBundle" in name:
            counts["support_bundle"] += 1
        elif "CommonClauseSegment" in name:
            counts["common_segment"] += 1
        elif "CommonClauseBundle" in name:
            counts["common_bundle"] += 1
        elif "VaryingClauseSegment" in name:
            counts["varying_segment"] += 1
        elif "VaryingClauseBundle" in name:
            counts["varying_bundle"] += 1
        elif "SemanticBranch" in name:
            counts["branch"] += 1
    require(counts["atom_segment"] == 32, "atom segment count changed")
    require(counts["atom_bundle"] == 2, "atom bundle count changed")
    require(counts["support_segment"] == 64, "support segment count changed")
    require(counts["support_bundle"] == 4, "support bundle count changed")
    require(counts["common_segment"] == 192, "common segment count changed")
    require(counts["common_bundle"] == 12, "common bundle count changed")
    require(counts["varying_segment"] == 64, "varying segment count changed")
    require(counts["varying_bundle"] == 4, "varying bundle count changed")
    require(counts["branch"] == 2, "branch consumer count changed")
    import_only_markers = (
        "AtomBundle",
        "SupportBundle",
        "CommonClauseBundle",
        "VaryingClauseBundle",
    )
    import_only_names = {
        "SynchronizedFiveFanFin11AltDepth2SemanticAtoms.lean",
        "SynchronizedFiveFanFin11AltDepth2SemanticSupport.lean",
        "SynchronizedFiveFanFin11AltDepth2SemanticCommonClauses.lean",
        "SynchronizedFiveFanFin11AltDepth2SemanticVaryingClauses.lean",
    }
    for relative in project:
        if (
            any(marker in relative.name for marker in import_only_markers)
            or relative.name in import_only_names
        ):
            text = outputs[relative].decode().rstrip()
            require(
                not text.endswith("\nend"),
                f"unmatched end in import-only module: {relative}",
            )
    pilot = outputs[
        Path(
            "ErdosSzekeres/"
            "SynchronizedFiveFanFin11AltDepth2SemanticPilot.lean"
        )
    ].decode()
    require("public import" not in pilot, "pilot publicly reexports private branches")


def assert_corruptions_rejected(
    generator: dict[str, object],
    source: dict[str, object],
    outputs: dict[Path, bytes],
) -> None:
    validate_source = generator["validate_source_model"]
    validate_outputs = generator["validate_outputs"]

    blob = b"authenticated test blob"
    blob_hash = sha256(blob)
    generator["authenticate_blob"]("test", blob, blob_hash, len(blob))
    expect_failure(
        "artifact hash",
        lambda: generator["authenticate_blob"](
            "test", blob + b"!", blob_hash, len(blob)
        ),
    )

    damaged = clone_source(source)
    branch = generator["BRANCH_ORDER"][0]
    damaged["branches"][branch]["entries"] = damaged["branches"][branch][
        "entries"
    ][1:]
    expect_failure("deleted branch obligation", lambda: validate_source(damaged))

    damaged = clone_source(source)
    damaged["entry_by_id"][99999] = dict(damaged["entry_by_id"][1])
    expect_failure("unused source theorem", lambda: validate_source(damaged))

    damaged = clone_source(source)
    damaged["branches"][branch]["old_to_new"][962] = 962
    expect_failure("atom-961 remap", lambda: validate_source(damaged))

    damaged = clone_source(source)
    entries = list(damaged["branches"][branch]["entries"])
    entries[0] = dict(entries[0])
    entries[0]["old_clause"] = tuple(reversed(entries[0]["old_clause"]))
    damaged["branches"][branch]["entries"] = tuple(entries)
    expect_failure("branch core literal", lambda: validate_source(damaged))

    damaged = clone_source(source)
    units = list(damaged["branches"][branch]["units"])
    units[0]["literal"] = 15
    damaged["branches"][branch]["units"] = tuple(units)
    expect_failure("signed unit", lambda: validate_source(damaged))

    damaged = clone_source(source)
    first_id = damaged["union_ids"][0]
    damaged["membership"][first_id] ^= 1
    expect_failure("membership bit", lambda: validate_source(damaged))

    damaged = clone_source(source)
    damaged["branches"] = dict(reversed(list(damaged["branches"].items())))
    expect_failure("branch reorder", lambda: validate_source(damaged))

    target = Path(
        "ErdosSzekeres/"
        "SynchronizedFiveFanFin11AltDepth2SemanticBase.lean"
    )
    overlong = dict(outputs)
    overlong[target] = outputs[target] + (b"-- " + b"x" * 101 + b"\n")
    expect_failure("overlong line", lambda: validate_outputs(overlong))

    for token in generator["FORBIDDEN_TOKENS"]:
        corrupted = dict(outputs)
        corrupted[target] = outputs[target] + f"\n-- {token}\n".encode()
        expect_failure(
            f"forbidden token {token}", lambda value=corrupted: validate_outputs(value)
        )

    deleted = dict(outputs)
    del deleted[target]
    expect_failure("deleted module", lambda: validate_outputs(deleted))

    extra_clause = dict(outputs)
    extra_clause[target] = outputs[target] + (
        b"\ntheorem synchronizedFiveFanFin11AltDepth2Semantic_clause99999 : True := "
        b"by trivial\n"
    )
    expect_failure("unused semantic theorem", lambda: validate_outputs(extra_clause))

    legacy_atom = dict(outputs)
    atom_target = Path(
        "ErdosSzekeres/"
        "SynchronizedFiveFanFin11AltDepth2SemanticAtomSegment000.lean"
    )
    legacy_atom[atom_target] = outputs[atom_target].replace(
        b"SynchronizedFiveFanFin11OriginalAtom0001",
        b"SynchronizedFiveFanFin11SemanticAtom0001",
        1,
    )
    expect_failure("legacy semantic atom", lambda: validate_outputs(legacy_atom))

    import_overflow = dict(outputs)
    imports = b"".join(
        f"import ErdosSzekeres.Fake{index:02d}\n".encode() for index in range(17)
    )
    import_overflow[target] = outputs[target] + imports
    expect_failure("import fan-in", lambda: validate_outputs(import_overflow))

    cycle = dict(outputs)
    cycle[target] = outputs[target].replace(
        b"public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticInterface",
        b"public import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase",
        1,
    )
    expect_failure("import cycle", lambda: validate_outputs(cycle))

    globals_dict = validate_outputs.__globals__
    old_cap = globals_dict["MAXIMUM_TOTAL_BYTES"]
    globals_dict["MAXIMUM_TOTAL_BYTES"] = sum(map(len, outputs.values())) - 1
    try:
        expect_failure("active source cap", lambda: validate_outputs(outputs))
    finally:
        globals_dict["MAXIMUM_TOTAL_BYTES"] = old_cap


def main() -> None:
    require(sha256(CONTROL.read_bytes()) == EXPECTED_CONTROL_SHA256, "control hash")
    generator = runpy.run_path(str(GENERATOR), run_name="__source_test__")
    control = runpy.run_path(str(CONTROL), run_name="__control_test__")
    source = generator["semantic_source"](ROOT)
    generator["validate_source_model"](source)
    require(
        generator["canonical_formula_bytes"](source["rows"])
        == generator["canonical_formula_bytes"](control["full_formula"]()),
        "full formula differs byte-for-byte from the frozen control",
    )

    outputs = generator["generated_project_outputs"](source)
    generator["add_run_outputs"](source, outputs)
    generator["validate_outputs"](outputs)
    require(len(outputs) == 386, "total generated file count changed")
    assert_exact_clause_coverage(source, outputs)
    assert_branch_consumers(generator, source, outputs)
    assert_module_partition(generator, outputs)

    second = generator["generated_project_outputs"](source)
    generator["add_run_outputs"](source, second)
    generator["validate_outputs"](second)
    first_hashes = {str(path): sha256(data) for path, data in outputs.items()}
    second_hashes = {str(path): sha256(data) for path, data in second.items()}
    require(first_hashes == second_hashes, "renderer is not byte-deterministic")
    assert_corruptions_rejected(generator, source, outputs)
    print(
        "ok: 16702 semantic clauses, 6158 groups, 1881 atoms, "
        "383 Lean modules; corruption suite passed"
    )


if __name__ == "__main__":
    main()
