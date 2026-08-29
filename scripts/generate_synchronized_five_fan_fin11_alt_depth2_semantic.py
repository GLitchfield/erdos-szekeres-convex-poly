#!/usr/bin/env python3
"""Render the frozen two-branch Fin11 alternate-depth-two semantic source.

This program is deliberately a source renderer, not a proof checker.  It
authenticates the frozen CNF/core/LRAT/map quartets and reconstructs their
semantic obligations in the stable original 1--1881 vocabulary before it
writes anything.  Lean and the certificate generators are separate gates.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import itertools
import json
from pathlib import Path
import re
import runpy
from typing import Iterable, Sequence


N = 11
TRIPLES = tuple(itertools.combinations(range(N), 3))
QUADS = tuple(itertools.combinations(range(N), 4))
FIVES = tuple(itertools.combinations(range(N), 5))
SIXES = tuple(itertools.combinations(range(N), 6))
TVAR = {triple: index + 1 for index, triple in enumerate(TRIPLES)}
QVAR = {quad: 166 + index for index, quad in enumerate(QUADS)}
FVAR = {five: 496 + index for index, five in enumerate(FIVES)}
LBAD = {five: 958 + index for index, five in enumerate(FIVES)}
UBAD = {five: 1420 + index for index, five in enumerate(FIVES)}

TASK_REL = Path("runs/agents/20260820-fin11-all-cubes-execution/semantic/task.json")
LEDGER_REL = Path(
    "runs/agents/20260820-fin11-all-cubes-planning/"
    "shallow-semantic-source/source-ledger.json"
)
RUN_REL = Path("runs/fin11-synchronized-five-fan-alt-depth2-semantic")
CONTROL_REL = Path("scripts/generate_synchronized_five_fan_fin11_semantic.py")
PARENT_REL = Path("runs/agents/20260812-frontier-cycle/fin11/core")
ALTERNATE_REL = Path(
    "runs/agents/20260812-promotion-wave/fin11-cubes/alternate-015-111"
)

EXPECTED_TASK_SHA256 = (
    "d167fe9e05bcbd2bfb29302e86624e481fbb714619545a6647b2afbb7f36a45c"
)
EXPECTED_INPUTS = {
    "AGENTS.md": "c13118d6722e1ebe0fa4cea04ce4b1b3053906129d50b05c6f40017fef23ae31",
    str(LEDGER_REL):
        "69cde2bee3f49af0916f00cd15bb6211646fe597f031770800e90dd3d64badff",
    "runs/agents/20260820-fin11-all-cubes-planning/root-plan/execution-plan.md":
        "3f6d8f5ef4db6a21100ed690f01feebcdef9bbc8fc2c388f4c44bd8f19b8bdce",
    "runs/agents/20260820-fin11-all-cubes-planning/root-plan/import-width-ledger.json":
        "112a4de50a69429b111c31208b1e61930b6e2f0fc9270d60cf27da4665498f52",
    "runs/agents/20260820-fin11-all-cubes-planning/shallow-semantic-source/report.md":
        "ca33cf11a5d04326b9a05f2a002df62877fd9e1ef9deffbd2e0a8ffb9d300bfe",
    str(CONTROL_REL):
        "32d0687ebb7fb4411afaf0fc496da9fe780694a89de11fb6dc776df390ad05d2",
    "scripts/test_generate_synchronized_five_fan_fin11_semantic.py":
        "825f3ec958e98d22872d0a5cf7c562875396f611a548183ecf623bfb539df641",
    "ErdosSzekeres/SynchronizedFiveFanFin11SemanticInterface.lean":
        "e91aeb4630e25c42e40b90bf3cff3d7bce2a05202a2fadd42e85d60158101ba3",
    str(ALTERNATE_REL / "manifest.json"):
        "39c6076a9b5e66ba4584d6daaa0135b7fe87363aaac75d3e28e7e1fde9055126",
    str(PARENT_REL / "core.cnf"):
        "50cf18bc1b14ad5c6ded5086a0437e664cdda4411c686f70c55ac6455070ab13",
    str(PARENT_REL / "core-map.json"):
        "afb118f4aecdb2eb831845b9a28ca43588496ef9951fd2aedd6510c890ef7d68",
}

BRANCH_ORDER = ("v015-0_v111-1", "v015-1_v111-1")
BRANCHES = {
    "v015-0_v111-1": {
        "stem": "SynchronizedFiveFanFin11AltDepth2RightLeft",
        "consumer": "SynchronizedFiveFanFin11AltDepth2SemanticBranchV0150V1111",
        "turns": ("right", "left"),
        "units": (-15, 111),
        "variables": 1880,
        "core_clauses": 14816,
        "semantic_clauses": 14814,
        "semantic_groups": 5417,
        "additions": 126630,
        "lrat_bytes": 64262475,
        "lrat_hints": 4397627,
        "final_clause_id": 141446,
        "family_counts": {
            "one_change": 2540,
            "strong_quad_definition": 2540,
            "strong_five_definition": 2470,
            "lower_bad_definition": 1965,
            "upper_bad_definition": 1927,
            "no_strong_six": 397,
            "no_synchronized_lower": 1436,
            "no_synchronized_upper": 1539,
        },
        "family_group_counts": {
            "one_change": 330,
            "strong_quad_definition": 330,
            "strong_five_definition": 462,
            "lower_bad_definition": 461,
            "upper_bad_definition": 462,
            "no_strong_six": 397,
            "no_synchronized_lower": 1436,
            "no_synchronized_upper": 1539,
        },
        "digests": {
            "semantic_ids":
                "0279cdd99b045ab3b7d5b28c85bab8bdd5ab8a5037390ab23781325841600f8a",
            "group_ids":
                "c784659028048f34f8af6f9ac2289d9ba8549f588bd3056ea831f78a7b2bfacc",
            "selected_base_ids":
                "23571ea921dd822eee0afcd1ec29111fea8c0fcb729e3b6c42bc54fbaafd8e66",
            "variable_map":
                "7dbb7e5beedb50136a16d24cc8085d2c19f6d34ec6f6bb8d36c647ff310d4990",
            "ordered_core_mapping":
                "6299c0b87a14a91f92e0ca3e42ee160943e8fb5cc7b612fcf893ce9ac762cb07",
        },
        "import_width": {
            "segments": 256,
            "peak_imported_clauses": 1763,
            "peak_import_segment": 239,
            "peak_carry_input_bytes": 145159,
            "peak_carry_segment": 239,
            "total_carry_bytes": 20614425,
            "maximum_additions_per_segment": 912,
        },
        "artifacts": {
            "child.cnf": (
                688280,
                "08131822ab2150e0fb764d794bd345d4b0a4f786d07a942bf49f7e9e277e1ae0",
            ),
            "core/core.cnf": (
                504981,
                "91413958440c383c8c2f3c75795db9c4935eb6a537786fe0a1ae805c8974084e",
            ),
            "core/core.lrat": (
                64262475,
                "041d1d9d71c41b810636bd9fc1a0db320f16b873acce6c213a27bf38a444ee73",
            ),
            "core/core-map.json": (
                1633146,
                "83cfe254a7935d12eb016d9b98e80701176100cb272fe73361bdd216dd57699e",
            ),
        },
    },
    "v015-1_v111-1": {
        "stem": "SynchronizedFiveFanFin11AltDepth2LeftLeft",
        "consumer": "SynchronizedFiveFanFin11AltDepth2SemanticBranchV0151V1111",
        "turns": ("left", "left"),
        "units": (15, 111),
        "variables": 1881,
        "core_clauses": 14911,
        "semantic_clauses": 14909,
        "semantic_groups": 5462,
        "additions": 126773,
        "lrat_bytes": 63652570,
        "lrat_hints": 4311453,
        "final_clause_id": 141684,
        "family_counts": {
            "one_change": 2544,
            "strong_quad_definition": 2554,
            "strong_five_definition": 2477,
            "lower_bad_definition": 2149,
            "upper_bad_definition": 1769,
            "no_strong_six": 398,
            "no_synchronized_lower": 1615,
            "no_synchronized_upper": 1403,
        },
        "family_group_counts": {
            "one_change": 330,
            "strong_quad_definition": 330,
            "strong_five_definition": 462,
            "lower_bad_definition": 462,
            "upper_bad_definition": 462,
            "no_strong_six": 398,
            "no_synchronized_lower": 1615,
            "no_synchronized_upper": 1403,
        },
        "digests": {
            "semantic_ids":
                "ef2a2590f29f490b541e15a54f241596fc70e9940534b010c13bc84342159b5c",
            "group_ids":
                "93f2dd31552e5763729a92f869e8e2966a9830fd581f213aca2f50f08d0fba56",
            "selected_base_ids":
                "5134e9a3be3c1bda8375b10c32e6351600bfa49dff0f7389864b9b99699b7c28",
            "variable_map":
                "39cba89db6a68193fb744c496f5e78e60e5270552cee1e5630565c7ac1120aac",
            "ordered_core_mapping":
                "f447579a4a75a6ef6db298e8b2e9620fbc59a622a43dde020e742e9e21a77dc8",
        },
        "import_width": {
            "segments": 256,
            "peak_imported_clauses": 1736,
            "peak_import_segment": 198,
            "peak_carry_input_bytes": 141110,
            "peak_carry_segment": 243,
            "total_carry_bytes": 21557686,
            "maximum_additions_per_segment": 814,
        },
        "artifacts": {
            "child.cnf": (
                688279,
                "a16ee4abb6a6c85417c2c44583492b981d3e2920a83561e1fdf18d88a034481b",
            ),
            "core/core.cnf": (
                512486,
                "876f979c837db789d9f2189a0a4d78efe3271e4f1a6416cbe48a4e759530960a",
            ),
            "core/core.lrat": (
                63652570,
                "0e27c0acc9d700acbc9ef69dfd6769f1f1263d3e392d38814a8b55d21968eeee",
            ),
            "core/core-map.json": (
                1635532,
                "8d3f050da30c3509983ad71d8585bf03ba8986367df835c9287985d236441768",
            ),
        },
    },
}

EXPECTED_SHARED = {
    "semantic_clause_union": 16702,
    "semantic_clause_intersection": 13021,
    "semantic_clause_varying": 3681,
    "mask_histogram": {1: 1793, 2: 1888, 3: 13021},
    "group_union": 6158,
    "groups_represented_by_common_clauses": 4705,
    "groups_present_in_both": 4721,
    "disjoint_witness_groups": 16,
    "helper_blocks": 1846,
    "family_clause_counts": {
        "one_change": 2602,
        "strong_quad_definition": 2605,
        "strong_five_definition": 2527,
        "lower_bad_definition": 2546,
        "upper_bad_definition": 2310,
        "no_strong_six": 424,
        "no_synchronized_lower": 1876,
        "no_synchronized_upper": 1812,
    },
    "family_group_counts": {
        "one_change": 330,
        "strong_quad_definition": 330,
        "strong_five_definition": 462,
        "lower_bad_definition": 462,
        "upper_bad_definition": 462,
        "no_strong_six": 424,
        "no_synchronized_lower": 1876,
        "no_synchronized_upper": 1812,
    },
    "digests": {
        "semantic_union_ids":
            "5bf22d9b79c224c5b41e79fb144f4362e848b3f968b8f075478fb620ac2154ae",
        "semantic_intersection_ids":
            "126dad8b14df377fce4bf0280ee0a1000f4afe81a041c6c303180ffd14186f43",
    },
}

ATOM_SEGMENTS = 32
SUPPORT_SEGMENTS = 64
COMMON_CLAUSE_SEGMENTS = 192
VARYING_CLAUSE_SEGMENTS = 64
IMPORT_FAN_IN = 16
EXPECTED_PROJECT_MODULES = 383
EXPECTED_TOTAL_FILES = 386
MAXIMUM_TOTAL_BYTES = 128 * 1024 * 1024
MAXIMUM_TOTAL_LINES = 2_000_000
MAXIMUM_SEGMENT_BYTES = 2 * 1024 * 1024
MAXIMUM_BRANCH_BYTES = 8 * 1024 * 1024
MAXIMUM_IMPORT_ONLY_BYTES = 64 * 1024
MAXIMUM_COLUMNS = 100
FORBIDDEN_TOKENS = (
    "sorry",
    "admit",
    "axiom",
    "unsafe",
    "native_decide",
    "maxHeartbeats 0",
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_bytes(value: object) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode()


def canonical_formula_bytes(rows: Sequence[dict[str, object]]) -> bytes:
    serial = []
    for row in rows:
        serial.append({
            "family": row["family"],
            "index": row["index"],
            "old_clause": row["old_clause"],
            "semantic_id": row["semantic_id"],
        })
    return canonical_bytes(serial)


def authenticate_blob(
    label: str,
    data: bytes,
    expected_hash: str,
    expected_bytes: int | None = None,
) -> None:
    if expected_bytes is not None and len(data) != expected_bytes:
        raise ValueError(f"frozen input byte count mismatch: {label}")
    if digest(data) != expected_hash:
        raise ValueError(f"frozen input hash mismatch: {label}")


def read_frozen_inputs(repo: Path) -> dict[str, bytes]:
    frozen = {}
    for relative, expected in EXPECTED_INPUTS.items():
        data = (repo / relative).read_bytes()
        authenticate_blob(relative, data, expected)
        frozen[relative] = data
    task_data = (repo / TASK_REL).read_bytes()
    authenticate_blob(str(TASK_REL), task_data, EXPECTED_TASK_SHA256)
    frozen[str(TASK_REL)] = task_data
    for branch in BRANCH_ORDER:
        for suffix, (expected_bytes, expected_hash) in BRANCHES[branch][
            "artifacts"
        ].items():
            relative = ALTERNATE_REL / branch / suffix
            data = (repo / relative).read_bytes()
            authenticate_blob(
                str(relative), data, expected_hash, expected_bytes
            )
            frozen[str(relative)] = data
    return frozen


def parse_dimacs(data: bytes) -> tuple[int, tuple[tuple[int, ...], ...]]:
    variables = expected = None
    clauses: list[tuple[int, ...]] = []
    pending: list[int] = []
    for raw in data.decode().splitlines():
        row = raw.strip()
        if not row or row.startswith("c"):
            continue
        if row.startswith("p"):
            _, kind, variables_text, expected_text = row.split()
            if kind != "cnf":
                raise ValueError("not CNF")
            variables = int(variables_text)
            expected = int(expected_text)
            continue
        for value in map(int, row.split()):
            if value == 0:
                clauses.append(tuple(pending))
                pending = []
            else:
                pending.append(value)
    if variables is None or expected is None or pending:
        raise ValueError("malformed DIMACS")
    if len(clauses) != expected:
        raise ValueError("DIMACS clause count mismatch")
    return variables, tuple(clauses)


def quad_triples(quad: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    a, b, c, d = quad
    return ((a, b, c), (a, b, d), (a, c, d), (b, c, d))


def blocker(
    variables: tuple[int, ...], bits: tuple[bool, ...]
) -> tuple[int, ...]:
    return tuple(-var if bit else var for var, bit in zip(variables, bits))


def full_formula() -> tuple[dict[str, object], ...]:
    """Independently reconstruct the frozen 26,862-row semantic formula."""
    rows: list[dict[str, object]] = []

    def add(
        family: str, index: tuple[object, ...], clause: tuple[int, ...]
    ) -> None:
        rows.append({
            "semantic_id": len(rows) + 1,
            "family": family,
            "index": index,
            "old_clause": tuple(clause),
        })

    for quad in QUADS:
        tvars = tuple(TVAR[triple] for triple in quad_triples(quad))
        for bits in itertools.product((False, True), repeat=4):
            if sum(a != b for a, b in zip(bits, bits[1:])) > 1:
                add("one_change", (quad,), blocker(tvars, bits))
        for bits in itertools.product((False, True), repeat=4):
            strong = bits[0] == bits[1] and bits[2] == bits[3]
            qliteral = QVAR[quad] if strong else -QVAR[quad]
            add(
                "strong_quad_definition",
                (quad,),
                blocker(tvars, bits) + (qliteral,),
            )
    for five in FIVES:
        qvars = tuple(QVAR[quad] for quad in itertools.combinations(five, 4))
        for qvar in qvars:
            add("strong_five_definition", (five,), (-FVAR[five], qvar))
        add(
            "strong_five_definition",
            (five,),
            (FVAR[five], *(-qvar for qvar in qvars)),
        )
        tvars = tuple(TVAR[triple] for triple in itertools.combinations(five, 3))
        add("lower_bad_definition", (five,), (-LBAD[five], FVAR[five]))
        add(
            "lower_bad_definition",
            (five,),
            (-LBAD[five], *(-tvar for tvar in tvars)),
        )
        for tvar in tvars:
            add(
                "lower_bad_definition",
                (five,),
                (-FVAR[five], tvar, LBAD[five]),
            )
        add("upper_bad_definition", (five,), (-UBAD[five], FVAR[five]))
        add(
            "upper_bad_definition",
            (five,),
            (-UBAD[five], *tvars),
        )
        for tvar in tvars:
            add(
                "upper_bad_definition",
                (five,),
                (-FVAR[five], -tvar, UBAD[five]),
            )
    for six in SIXES:
        clause = tuple(-QVAR[quad] for quad in itertools.combinations(six, 4))
        add("no_strong_six", (six,), clause)
    for side in SIXES:
        side_set = set(side)
        for pivot in range(N):
            if pivot in side_set:
                continue
            for lower, bad, family in (
                (True, LBAD, "no_synchronized_lower"),
                (False, UBAD, "no_synchronized_upper"),
            ):
                clause = []
                for u, v in itertools.combinations(side, 2):
                    triple = tuple(sorted((pivot, u, v)))
                    required = triple[1] in side_set if lower else triple[1] == pivot
                    clause.append(-TVAR[triple] if required else TVAR[triple])
                clause.extend(bad[five] for five in itertools.combinations(side, 5))
                add(family, (side, pivot), tuple(clause))
    if len(rows) != 26862:
        raise ValueError("full semantic formula dimension changed")
    clauses = {row["old_clause"] for row in rows}
    if len(clauses) != len(rows):
        raise ValueError("full semantic formula is no longer clause-unique")
    return tuple(rows)


def group_value(entry: dict[str, object]) -> list[object]:
    return [entry["family"], entry["index"]]


def group_token(entry: dict[str, object]) -> str:
    return json.dumps(group_value(entry), sort_keys=True, separators=(",", ":"))


def remap_clause(
    clause: tuple[int, ...], old_to_new: dict[int, int]
) -> tuple[int, ...]:
    return tuple(
        (1 if literal > 0 else -1) * old_to_new[abs(literal)]
        for literal in clause
    )


def reconstruct_branch(
    branch: str,
    rows: tuple[dict[str, object], ...],
    parent_ids: tuple[int, ...],
    parent_clauses: tuple[tuple[int, ...], ...],
    frozen: dict[str, bytes],
) -> dict[str, object]:
    spec = BRANCHES[branch]
    prefix = ALTERNATE_REL / branch
    child_variables, child_clauses = parse_dimacs(frozen[str(prefix / "child.cnf")])
    core_variables, core_clauses = parse_dimacs(
        frozen[str(prefix / "core/core.cnf")]
    )
    core_map = json.loads(frozen[str(prefix / "core/core-map.json")])
    if (child_variables, len(child_clauses)) != (1881, 19209):
        raise ValueError(f"{branch}: child dimensions changed")
    if child_clauses[:19207] != parent_clauses:
        raise ValueError(f"{branch}: child prefix differs from parent")
    if (core_variables, len(core_clauses)) != (
        spec["variables"], spec["core_clauses"]
    ):
        raise ValueError(f"{branch}: core dimensions changed")
    core_metadata = core_map["core"]
    expected_core_metadata = {
        "additions": spec["additions"],
        "base_clauses": spec["core_clauses"],
        "final_clause_id": spec["final_clause_id"],
        "variables": spec["variables"],
        "cnf_sha256": spec["artifacts"]["core/core.cnf"][1],
        "lrat_sha256": spec["artifacts"]["core/core.lrat"][1],
    }
    if core_metadata != expected_core_metadata:
        raise ValueError(f"{branch}: core metadata changed")
    selected_base_ids = tuple(map(int, core_map["selected_base_ids"]))
    old_to_new = {
        int(old): int(new)
        for old, new in core_map["variable_map_old_to_new"].items()
    }
    new_to_old = {new: old for old, new in old_to_new.items()}
    if len(old_to_new) != spec["variables"]:
        raise ValueError(f"{branch}: variable-map cardinality changed")
    if tuple(sorted(new_to_old)) != tuple(range(1, spec["variables"] + 1)):
        raise ValueError(f"{branch}: variable map is not dense")
    if branch == BRANCH_ORDER[0]:
        expected = {old: old for old in range(1, 961)}
        expected.update({old: old - 1 for old in range(962, 1882)})
        if old_to_new != expected or 961 in old_to_new:
            raise ValueError("negative-15 atom-961 remap changed")
    elif old_to_new != {old: old for old in range(1, 1882)}:
        raise ValueError("positive-15 identity map changed")
    entries = []
    units = []
    if len(selected_base_ids) != len(core_clauses):
        raise ValueError(f"{branch}: selected/core lengths differ")
    for core_id, (base_id, dense_clause) in enumerate(
        zip(selected_base_ids, core_clauses), 1
    ):
        source_clause = child_clauses[base_id - 1]
        if remap_clause(source_clause, old_to_new) != dense_clause:
            raise ValueError(f"{branch}: remap mismatch at core clause {core_id}")
        if base_id <= 19207:
            semantic_id = parent_ids[base_id - 1]
            source = rows[semantic_id - 1]
            if source["old_clause"] != source_clause:
                raise ValueError(f"{branch}: semantic source mismatch at {core_id}")
            entry = dict(source)
            entry.update({
                "core_id": core_id,
                "base_id": base_id,
                "dense_clause": dense_clause,
            })
            entries.append(entry)
        else:
            if len(source_clause) != 1:
                raise ValueError(f"{branch}: non-unit assignment row {base_id}")
            units.append({
                "core_id": core_id,
                "base_id": base_id,
                "literal": source_clause[0],
                "dense_clause": dense_clause,
            })
    counts = Counter(entry["family"] for entry in entries)
    groups = {group_token(entry) for entry in entries}
    if len(entries) != spec["semantic_clauses"]:
        raise ValueError(f"{branch}: semantic-clause count changed")
    if dict(counts) != spec["family_counts"]:
        raise ValueError(f"{branch}: semantic-family counts changed")
    group_counts = Counter(json.loads(group)[0] for group in groups)
    if len(groups) != spec["semantic_groups"]:
        raise ValueError(f"{branch}: semantic-group count changed")
    if dict(group_counts) != spec["family_group_counts"]:
        raise ValueError(f"{branch}: family/group counts changed")
    if tuple(unit["literal"] for unit in units) != spec["units"]:
        raise ValueError(f"{branch}: signed units changed")
    semantic_ids = sorted(entry["semantic_id"] for entry in entries)
    if digest(canonical_bytes(semantic_ids)) != spec["digests"]["semantic_ids"]:
        raise ValueError(f"{branch}: semantic-ID digest changed")
    selected_digest = digest(canonical_bytes(list(selected_base_ids)))
    if selected_digest != spec["digests"]["selected_base_ids"]:
        raise ValueError(f"{branch}: selected-base-ID digest changed")
    mapping_pairs = [[old, old_to_new[old]] for old in sorted(old_to_new)]
    if digest(canonical_bytes(mapping_pairs)) != spec["digests"]["variable_map"]:
        raise ValueError(f"{branch}: variable-map digest changed")
    canonical_groups = [json.loads(item) for item in sorted(groups)]
    if digest(canonical_bytes(canonical_groups)) != spec["digests"]["group_ids"]:
        raise ValueError(f"{branch}: semantic-group digest changed")
    return {
        "name": branch,
        "entries": tuple(entries),
        "units": tuple(units),
        "all_entries": tuple(sorted((*entries, *units), key=lambda row: row["core_id"])),
        "old_to_new": old_to_new,
        "new_to_old": new_to_old,
        "selected_base_ids": selected_base_ids,
        "groups": groups,
    }


def semantic_source(repo: Path) -> dict[str, object]:
    frozen = read_frozen_inputs(repo)
    rows = full_formula()
    control = runpy.run_path(str(repo / CONTROL_REL), run_name="__frozen_control__")
    if canonical_formula_bytes(rows) != canonical_formula_bytes(control["full_formula"]()):
        raise ValueError("new/control full-formula reconstructions differ")
    parent_variables, parent_clauses = parse_dimacs(
        frozen[str(PARENT_REL / "core.cnf")]
    )
    parent_map = json.loads(frozen[str(PARENT_REL / "core-map.json")])
    parent_ids = tuple(map(int, parent_map["selected_base_ids"]))
    if (parent_variables, len(parent_clauses), len(parent_ids)) != (
        1881, 19207, 19207
    ):
        raise ValueError("parent dimensions changed")
    reconstructed = tuple(rows[item - 1]["old_clause"] for item in parent_ids)
    if reconstructed != parent_clauses:
        raise ValueError("formula does not reconstruct the parent core")
    branches = {
        branch: reconstruct_branch(
            branch, rows, parent_ids, parent_clauses, frozen
        )
        for branch in BRANCH_ORDER
    }
    membership: dict[int, int] = defaultdict(int)
    entry_by_id: dict[int, dict[str, object]] = {}
    group_membership: dict[str, int] = defaultdict(int)
    for bit, branch in enumerate(BRANCH_ORDER):
        for entry in branches[branch]["entries"]:
            semantic_id = int(entry["semantic_id"])
            membership[semantic_id] |= 1 << bit
            entry_by_id[semantic_id] = entry
        for group in branches[branch]["groups"]:
            group_membership[group] |= 1 << bit
    union_ids = tuple(sorted(membership))
    common_ids = tuple(item for item in union_ids if membership[item] == 3)
    varying_ids = tuple(item for item in union_ids if membership[item] != 3)
    mask_counts = Counter(membership.values())
    if len(union_ids) != EXPECTED_SHARED["semantic_clause_union"]:
        raise ValueError("semantic union count changed")
    if len(common_ids) != EXPECTED_SHARED["semantic_clause_intersection"]:
        raise ValueError("semantic intersection count changed")
    if len(varying_ids) != EXPECTED_SHARED["semantic_clause_varying"]:
        raise ValueError("semantic varying count changed")
    if dict(mask_counts) != EXPECTED_SHARED["mask_histogram"]:
        raise ValueError("semantic membership histogram changed")
    if digest(canonical_bytes(list(union_ids))) != EXPECTED_SHARED["digests"][
        "semantic_union_ids"
    ]:
        raise ValueError("semantic union digest changed")
    if digest(canonical_bytes(list(common_ids))) != EXPECTED_SHARED["digests"][
        "semantic_intersection_ids"
    ]:
        raise ValueError("semantic intersection digest changed")
    union_entries = tuple(entry_by_id[item] for item in union_ids)
    first_group_entry = {}
    for entry in union_entries:
        first_group_entry.setdefault(group_token(entry), entry)
    group_counts = Counter(
        first_group_entry[token]["family"] for token in group_membership
    )
    if len(group_membership) != EXPECTED_SHARED["group_union"]:
        raise ValueError("semantic group union changed")
    if dict(group_counts) != EXPECTED_SHARED["family_group_counts"]:
        raise ValueError("semantic family/group union changed")
    family_counts = Counter(entry["family"] for entry in union_entries)
    if dict(family_counts) != EXPECTED_SHARED["family_clause_counts"]:
        raise ValueError("semantic family/clause union changed")
    common_groups = {
        group_token(entry_by_id[item]) for item in common_ids
    }
    if len(common_groups) != EXPECTED_SHARED[
        "groups_represented_by_common_clauses"
    ]:
        raise ValueError("common-clause group count changed")
    if sum(mask == 3 for mask in group_membership.values()) != EXPECTED_SHARED[
        "groups_present_in_both"
    ]:
        raise ValueError("group membership intersection changed")
    return {
        "rows": rows,
        "branches": branches,
        "membership": dict(membership),
        "entry_by_id": entry_by_id,
        "union_ids": union_ids,
        "common_ids": common_ids,
        "varying_ids": varying_ids,
        "union_entries": union_entries,
        "group_membership": dict(group_membership),
        "frozen_hashes": {
            relative: digest(data) for relative, data in frozen.items()
        },
        "control": control,
    }


def validate_source_model(source: dict[str, object]) -> None:
    """Reject deletions, additions, remap drift, or membership corruption."""
    rows = source["rows"]
    if len(rows) != 26862 or len({row["old_clause"] for row in rows}) != 26862:
        raise ValueError("full-formula coverage changed")
    branches = source["branches"]
    if tuple(branches) != BRANCH_ORDER:
        raise ValueError("branch order changed")
    rebuilt_membership: dict[int, int] = defaultdict(int)
    rebuilt_entries: dict[int, dict[str, object]] = {}
    rebuilt_groups: dict[str, int] = defaultdict(int)
    for bit, branch in enumerate(BRANCH_ORDER):
        data = branches[branch]
        spec = BRANCHES[branch]
        entries = data["entries"]
        units = data["units"]
        if len(entries) != spec["semantic_clauses"] or len(units) != 2:
            raise ValueError(f"{branch}: exact obligation coverage changed")
        if tuple(item["literal"] for item in units) != spec["units"]:
            raise ValueError(f"{branch}: signed units changed")
        if tuple(item["core_id"] for item in data["all_entries"]) != tuple(
            range(1, spec["core_clauses"] + 1)
        ):
            raise ValueError(f"{branch}: dense core order changed")
        old_to_new = data["old_to_new"]
        if branch == BRANCH_ORDER[0]:
            if 961 in old_to_new or old_to_new.get(962) != 961:
                raise ValueError("negative branch atom-961 remap changed")
        elif any(old_to_new.get(old) != old for old in range(1, 1882)):
            raise ValueError("positive branch identity map changed")
        for entry in entries:
            semantic_id = int(entry["semantic_id"])
            if rows[semantic_id - 1]["old_clause"] != entry["old_clause"]:
                raise ValueError(f"{branch}: semantic row corruption")
            rebuilt_membership[semantic_id] |= 1 << bit
            rebuilt_entries[semantic_id] = entry
            rebuilt_groups[group_token(entry)] |= 1 << bit
    if rebuilt_membership != source["membership"]:
        raise ValueError("semantic membership corruption")
    if set(rebuilt_entries) != set(source["entry_by_id"]):
        raise ValueError("unused or missing semantic source theorem")
    if rebuilt_groups != source["group_membership"]:
        raise ValueError("group membership corruption")
    union_ids = tuple(sorted(rebuilt_membership))
    common_ids = tuple(item for item in union_ids if rebuilt_membership[item] == 3)
    varying_ids = tuple(item for item in union_ids if rebuilt_membership[item] != 3)
    if union_ids != source["union_ids"]:
        raise ValueError("semantic union ordering or coverage changed")
    if common_ids != source["common_ids"]:
        raise ValueError("common semantic layer changed")
    if varying_ids != source["varying_ids"]:
        raise ValueError("varying semantic layer changed")
    if len(union_ids) != 16702 or len(common_ids) != 13021:
        raise ValueError("shared semantic dimensions changed")
    if len(varying_ids) != 3681 or len(rebuilt_groups) != 6158:
        raise ValueError("varying clause or family/index dimensions changed")


def finset(vertices: tuple[int, ...]) -> str:
    return "{" + ", ".join(map(str, vertices)) + "}"


def original_atom_name(variable: int) -> str:
    return f"SynchronizedFiveFanFin11OriginalAtom{variable:04d}"


def original_atom_term(variable: int) -> str:
    return f"{original_atom_name(variable)} chi"


def triple_term(triple: tuple[int, ...]) -> str:
    a, b, c = triple
    return f"chi ⟨{a}, {b}, {c}, by decide, by decide⟩"


def public_header(imports: Sequence[tuple[str, bool]]) -> list[str]:
    lines = ["module", ""]
    for name, public in imports:
        lines.append(f"{'public ' if public else ''}import {name}")
    lines += [
        "",
        "@[expose] public section",
        "",
        "set_option maxRecDepth 30000",
        "set_option linter.unusedSimpArgs false",
        "",
        "namespace ErdosSzekeres",
        "",
    ]
    return lines


def close_module(lines: list[str]) -> bytes:
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines).encode()


def interface_text() -> bytes:
    lines = public_header((
        ("ErdosSzekeres.SynchronizedFiveFanFin11SemanticInterface", True),
        ("ErdosSzekeres.SynchronizedFiveFanFin11BranchInterface", True),
    ))
    lines += [
        "/-- The two frozen alternate-depth-two Boolean positions. -/",
        "abbrev Fin11AltDepth2Assignment := Fin 2 → Bool",
        "",
        "/-- Geometric meaning of the two frozen Boolean positions. -/",
        "def Fin11AltDepth2Holds",
        "    (sigma : Fin11AltDepth2Assignment) (chi : TripleColoring 11) : Prop :=",
        f"  ({triple_term((0, 2, 8))} = Turn.left ↔ sigma 0 = true) ∧",
        f"    ({triple_term((3, 4, 6))} = Turn.left ↔ sigma 1 = true)",
        "",
        "theorem fin11AltDepth2Holds_position0",
        "    {sigma : Fin11AltDepth2Assignment} {chi : TripleColoring 11}",
        "    (h : Fin11AltDepth2Holds sigma chi) :",
        f"    {triple_term((0, 2, 8))} = Turn.left ↔ sigma 0 = true := h.1",
        "",
        "theorem fin11AltDepth2Holds_position1",
        "    {sigma : Fin11AltDepth2Assignment} {chi : TripleColoring 11}",
        "    (h : Fin11AltDepth2Holds sigma chi) :",
        f"    {triple_term((3, 4, 6))} = Turn.left ↔ sigma 1 = true := h.2",
        "",
    ]
    return close_module(lines)


def base_text() -> bytes:
    lines = public_header((
        ("ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticInterface", True),
    ))
    lines += [
        "def Fin11AltDepth2StrongQuad",
        "    (chi : TripleColoring 11) (a b c d : Fin 11)",
        "    (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=",
        "  chi ⟨a, b, c, hab, hbc⟩ = chi ⟨a, b, d, hab, hbc.trans hcd⟩ ∧",
        "    chi ⟨a, c, d, hab.trans hbc, hcd⟩ = chi ⟨b, c, d, hbc, hcd⟩",
        "",
    ]
    return close_module(lines)


def atom_definition_lines(variable: int) -> list[str]:
    lines = [f"def {original_atom_name(variable)} (chi : TripleColoring 11) : Prop :="]
    if variable <= 165:
        lines.append(f"  {triple_term(TRIPLES[variable - 1])} = Turn.left")
    elif variable <= 495:
        a, b, c, d = QUADS[variable - 166]
        lines += [
            "  Fin11AltDepth2StrongQuad",
            f"    chi {a} {b} {c} {d} (by decide) (by decide) (by decide)",
        ]
    elif variable <= 957:
        lines.append(f"  IsStrongPolygonSet chi {finset(FIVES[variable - 496])}")
    elif variable <= 1419:
        five = FIVES[variable - 958]
        lines += [
            f"  IsStrongPolygonSet chi {finset(five)} ∧",
            f"    ¬IsCupSet chi {finset(five)}",
        ]
    else:
        five = FIVES[variable - 1420]
        lines += [
            f"  IsStrongPolygonSet chi {finset(five)} ∧",
            f"    ¬IsCapSet chi {finset(five)}",
        ]
    lines.append("")
    return lines


def atom_segment_text(index: int, variables: Sequence[int]) -> bytes:
    lines = public_header((
        ("ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticBase", True),
    ))
    lines += [f"/-! Stable original semantic atoms, segment {index:03d}. -/", ""]
    for variable in variables:
        lines += atom_definition_lines(variable)
    return close_module(lines)


def import_only_text(imports: Sequence[str], public: bool = True) -> bytes:
    lines = ["module", ""]
    for name in imports:
        lines.append(f"{'public ' if public else ''}import {name}")
    lines += [""]
    return "\n".join(lines).encode()


RENDER_REPLACEMENTS = (
    (
        "SynchronizedFiveFanFin11SemanticAtom",
        "SynchronizedFiveFanFin11OriginalAtom",
    ),
    (
        "SynchronizedFiveFanFin11SemanticStrongQuad",
        "Fin11AltDepth2StrongQuad",
    ),
    (
        "synchronizedFiveFanFin11Semantic_clause",
        "synchronizedFiveFanFin11AltDepth2Semantic_clause",
    ),
    (
        "synchronizedFiveFanFin11_strongSet_iff_mask",
        "fin11AltDepth2_strongSet_iff_mask",
    ),
    (
        "synchronizedFiveFanFin11_cupSet_iff_mask",
        "fin11AltDepth2_cupSet_iff_mask",
    ),
    (
        "synchronizedFiveFanFin11_capSet_iff_mask",
        "fin11AltDepth2_capSet_iff_mask",
    ),
    (
        "synchronizedFiveFanFin11_fiveSubset_mask",
        "fin11AltDepth2_fiveSubset_mask",
    ),
)


def transform_rendered_line(line: str) -> str:
    for old, new in RENDER_REPLACEMENTS:
        line = line.replace(old, new)
    return line


def prepare_control_renderer(source: dict[str, object]) -> dict[str, object]:
    control = source["control"]
    control["atom_name"] = original_atom_name
    control["atom_term"] = original_atom_term
    return control


def helper_blocks(source: dict[str, object]) -> tuple[tuple[str, ...], ...]:
    control = prepare_control_renderer(source)
    raw = control["semantic_helper_blocks"]({"entries": source["union_entries"]})
    blocks = tuple(
        tuple(transform_rendered_line(line) for line in block)
        for block in raw
    )
    if len(blocks) != EXPECTED_SHARED["helper_blocks"]:
        raise ValueError("semantic helper-block count changed")
    return blocks


def clause_block(
    source: dict[str, object], semantic_id: int
) -> tuple[str, ...]:
    control = prepare_control_renderer(source)
    source_entry = source["entry_by_id"][semantic_id]
    entry = dict(source_entry)
    entry["core_id"] = semantic_id
    entry["literals"] = tuple(entry["old_clause"])
    raw = control["semantic_clause_lines"](entry)
    return tuple(transform_rendered_line(line) for line in raw) + ("",)


def balanced_blocks(
    blocks: Sequence[tuple[str, tuple[str, ...]]], count: int
) -> tuple[tuple[tuple[str, tuple[str, ...]], ...], ...]:
    if len(blocks) < count:
        raise ValueError("too few blocks for nonempty deterministic partition")
    chunks: list[list[tuple[str, tuple[str, ...]]]] = [[] for _ in range(count)]
    weights = [0] * count
    ordered = sorted(
        blocks,
        key=lambda item: (-sum(len(line) + 1 for line in item[1]), item[0]),
    )
    for block in ordered:
        index = min(range(count), key=lambda item: (weights[item], item))
        chunks[index].append(block)
        weights[index] += sum(len(line) + 1 for line in block[1])
    if any(not chunk for chunk in chunks):
        raise ValueError("empty segment in deterministic partition")
    return tuple(
        tuple(sorted(chunk, key=lambda item: item[0])) for chunk in chunks
    )


def content_segment_text(
    module_title: str,
    dependency: str,
    blocks: Sequence[tuple[str, tuple[str, ...]]],
) -> bytes:
    lines = public_header(((dependency, True),))
    lines += [f"/-! {module_title}. -/", ""]
    for _, block in blocks:
        lines += list(block)
    return close_module(lines)


def assignment_holds_lines(branch: str) -> list[str]:
    first, second = BRANCHES[branch]["turns"]
    false_first = first == "right"
    return [
        "  have hholds : Fin11AltDepth2Holds",
        f"      ![{str(not false_first).lower()}, true] chi := by",
        "    unfold Fin11AltDepth2Holds",
        "    unfold SynchronizedFiveFanFin11TwoBitBranch at hbranch",
        "    rcases hbranch with ⟨h0, h1⟩",
        "    have htriple0 : synchronizedFiveFanFin11BranchTriple0 =",
        "        (⟨0, 2, 8, by decide, by decide⟩ : OrderedTriple 11) := by",
        "      unfold synchronizedFiveFanFin11BranchTriple0",
        "      congr",
        "    have htriple1 : synchronizedFiveFanFin11BranchTriple1 =",
        "        (⟨3, 4, 6, by decide, by decide⟩ : OrderedTriple 11) := by",
        "      unfold synchronizedFiveFanFin11BranchTriple1",
        "      congr",
        "    rw [htriple0] at h0",
        "    rw [htriple1] at h1",
        "    constructor",
        "    · simp [h0]",
        "    · simp [h1]",
    ]


def semantic_clause_application(entry: dict[str, object]) -> str:
    semantic_id = int(entry["semantic_id"])
    application = (
        f"synchronizedFiveFanFin11AltDepth2Semantic_clause{semantic_id:05d} chi"
    )
    family = str(entry["family"])
    if family == "one_change":
        application += " hone"
    elif family == "no_strong_six":
        application += " hnoStrong"
    elif family.startswith("no_synchronized_"):
        application += " hno"
    return application


def unit_refutation_name(literal: int) -> str:
    sign = "pos" if literal > 0 else "neg"
    return f"hunit_{sign}_{abs(literal):04d}"


def append_or_refutation(
    lines: list[str],
    entries: Sequence[dict[str, object]],
    start: int,
    stop: int,
    hypothesis: str,
    indent: str,
) -> None:
    if stop - start == 1:
        entry = entries[start]
        if "semantic_id" in entry:
            application = semantic_clause_application(entry).split()
        else:
            application = [unit_refutation_name(entry["literal"])]
        single_line = f"{indent}exact {' '.join(application)}"
        if len(single_line) <= MAXIMUM_COLUMNS:
            lines.append(single_line)
        else:
            first_line_count = min(2, len(application))
            lines.append(
                f"{indent}exact {' '.join(application[:first_line_count])}"
            )
            if len(application) > first_line_count:
                lines.append(
                    f"{indent}  {' '.join(application[first_line_count:])}"
                )
        lines.append(f"{indent}  {hypothesis}")
        return
    middle = start + (stop - start) // 2
    left = f"h{start:05d}_{middle:05d}"
    right = f"h{middle:05d}_{stop:05d}"
    lines.append(f"{indent}rcases {hypothesis} with {left} | {right}")
    lines.append(f"{indent}·")
    append_or_refutation(lines, entries, start, middle, left, indent + "  ")
    lines.append(f"{indent}·")
    append_or_refutation(lines, entries, middle, stop, right, indent + "  ")


def branch_consumer_text(source: dict[str, object], branch: str) -> bytes:
    spec = BRANCHES[branch]
    data = source["branches"][branch]
    stem = spec["stem"]
    imports = (
        ("ErdosSzekeres.SynchronizedFiveFanFin11BranchInterface", True),
        ("ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticCommonClauses", False),
        ("ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticVaryingClauses", False),
        (f"ErdosSzekeres.{stem}CheckpointLeaf", False),
    )
    lines = public_header(imports)
    first, second = spec["turns"]
    theorem_name = (
        "synchronizedFiveFanFin11PrimaryBranchForces_"
        f"{first}_{second}"
    )
    lines += [
        "",
        f"theorem {theorem_name} :",
        f"    SynchronizedFiveFanFin11BranchForces Turn.{first} Turn.{second} := by",
        "  intro chi hone hnoStrong hbranch",
        "  by_contra hno",
    ]
    lines += assignment_holds_lines(branch)
    for unit in data["units"]:
        literal = int(unit["literal"])
        position = 0 if abs(literal) == 15 else 1
        adapter = f"fin11AltDepth2Holds_position{position} hholds"
        theorem = unit_refutation_name(literal)
        atom = original_atom_term(abs(literal))
        lines += [f"  have {theorem} :"]
        if literal > 0:
            lines += [
                f"      ¬(¬{atom}) := by",
                "    intro hnot",
                "    apply hnot",
            ]
            lines.append(f"    exact ({adapter}).mpr (by decide)")
        else:
            lines += [f"      ¬{atom} := by", "    intro hatom"]
            lines.append(f"    exact Bool.noConfusion (({adapter}).mp hatom)")
    lines += ["  have hbad :=", f"    synchronizedFiveFanFin11_{stem}_lrat_unsat"]
    for dense in range(1, int(spec["variables"]) + 1):
        old = data["new_to_old"][dense]
        lines.append(f"      ({original_atom_term(old)})")
    lines.append(f"  unfold {stem}Checkpoint.bad at hbad")
    append_or_refutation(
        lines,
        data["all_entries"],
        0,
        len(data["all_entries"]),
        "hbad",
        "  ",
    )
    lines.append("")
    return close_module(lines)


def axiom_audit_text() -> bytes:
    lines = [
        "import ErdosSzekeres.SynchronizedFiveFanFin11AltDepth2SemanticPilot",
        "",
        "#print axioms",
        "  ErdosSzekeres.synchronizedFiveFanFin11PrimaryBranchForces_right_left",
        "#print axioms",
        "  ErdosSzekeres.synchronizedFiveFanFin11PrimaryBranchForces_left_left",
        "",
    ]
    return "\n".join(lines).encode()


def module_name(relative: Path) -> str:
    if relative.suffix != ".lean" or relative.parts[0] != "ErdosSzekeres":
        raise ValueError(f"not a generated project Lean module: {relative}")
    return ".".join(relative.with_suffix("").parts)


IMPORT_RE = re.compile(r"^(?:public )?import ([A-Za-z0-9_.]+)$", re.MULTILINE)
DECL_RE = re.compile(
    r"^(?:def|abbrev|theorem) ([A-Za-z0-9_]+)", re.MULTILINE
)


def source_metadata(relative: Path, data: bytes) -> dict[str, object]:
    text = data.decode()
    lines = text.splitlines()
    return {
        "path": str(relative),
        "sha256": digest(data),
        "bytes": len(data),
        "lines": len(lines),
        "maximum_column": max((len(line) for line in lines), default=0),
        "imports": IMPORT_RE.findall(text),
        "declarations": DECL_RE.findall(text),
    }


def generated_project_outputs(source: dict[str, object]) -> dict[Path, bytes]:
    validate_source_model(source)
    outputs: dict[Path, bytes] = {}
    prefix = "ErdosSzekeres/SynchronizedFiveFanFin11AltDepth2Semantic"
    outputs[Path(f"{prefix}Interface.lean")] = interface_text()
    outputs[Path(f"{prefix}Base.lean")] = base_text()

    variables = list(range(1, 1882))
    atom_sizes = [59] * 25 + [58] * 7
    start = 0
    atom_names = []
    for index, size in enumerate(atom_sizes):
        relative = Path(f"{prefix}AtomSegment{index:03d}.lean")
        outputs[relative] = atom_segment_text(index, variables[start:start + size])
        atom_names.append(module_name(relative))
        start += size
    if start != 1881:
        raise ValueError("atom partition changed")
    atom_bundle_names = []
    for index in range(2):
        relative = Path(f"{prefix}AtomBundle{index:02d}.lean")
        imports = atom_names[index * 16:(index + 1) * 16]
        outputs[relative] = import_only_text(imports)
        atom_bundle_names.append(module_name(relative))
    atoms_relative = Path(f"{prefix}Atoms.lean")
    outputs[atoms_relative] = import_only_text(atom_bundle_names)

    support_blocks = [
        (block[0], block) for block in helper_blocks(source)
    ]
    support_chunks = balanced_blocks(support_blocks, SUPPORT_SEGMENTS)
    support_names = []
    for index, chunk in enumerate(support_chunks):
        relative = Path(f"{prefix}SupportSegment{index:03d}.lean")
        outputs[relative] = content_segment_text(
            f"Alternate-depth-two semantic helpers, segment {index:03d}",
            module_name(atoms_relative),
            chunk,
        )
        support_names.append(module_name(relative))
    support_bundle_names = []
    for index in range(4):
        relative = Path(f"{prefix}SupportBundle{index:02d}.lean")
        imports = support_names[index * 16:(index + 1) * 16]
        outputs[relative] = import_only_text(imports)
        support_bundle_names.append(module_name(relative))
    support_relative = Path(f"{prefix}Support.lean")
    outputs[support_relative] = import_only_text(support_bundle_names)

    common_blocks = [
        (
            f"{group_token(source['entry_by_id'][semantic_id])}:"
            f"{semantic_id:05d}",
            clause_block(source, semantic_id),
        )
        for semantic_id in source["common_ids"]
    ]
    common_chunks = balanced_blocks(common_blocks, COMMON_CLAUSE_SEGMENTS)
    common_names = []
    for index, chunk in enumerate(common_chunks):
        relative = Path(f"{prefix}CommonClauseSegment{index:03d}.lean")
        outputs[relative] = content_segment_text(
            f"Common alternate-depth-two clauses, segment {index:03d}",
            module_name(support_relative),
            chunk,
        )
        common_names.append(module_name(relative))
    common_bundle_names = []
    for index in range(12):
        relative = Path(f"{prefix}CommonClauseBundle{index:02d}.lean")
        imports = common_names[index * 16:(index + 1) * 16]
        outputs[relative] = import_only_text(imports)
        common_bundle_names.append(module_name(relative))
    common_relative = Path(f"{prefix}CommonClauses.lean")
    outputs[common_relative] = import_only_text(common_bundle_names)

    varying_blocks = [
        (
            f"{group_token(source['entry_by_id'][semantic_id])}:"
            f"{semantic_id:05d}",
            clause_block(source, semantic_id),
        )
        for semantic_id in source["varying_ids"]
    ]
    varying_chunks = balanced_blocks(varying_blocks, VARYING_CLAUSE_SEGMENTS)
    varying_names = []
    for index, chunk in enumerate(varying_chunks):
        relative = Path(f"{prefix}VaryingClauseSegment{index:03d}.lean")
        outputs[relative] = content_segment_text(
            f"Varying alternate-depth-two clauses, segment {index:03d}",
            module_name(support_relative),
            chunk,
        )
        varying_names.append(module_name(relative))
    varying_bundle_names = []
    for index in range(4):
        relative = Path(f"{prefix}VaryingClauseBundle{index:02d}.lean")
        imports = varying_names[index * 16:(index + 1) * 16]
        outputs[relative] = import_only_text(imports)
        varying_bundle_names.append(module_name(relative))
    varying_relative = Path(f"{prefix}VaryingClauses.lean")
    outputs[varying_relative] = import_only_text(varying_bundle_names)

    branch_modules = []
    for branch in BRANCH_ORDER:
        relative = Path(
            "ErdosSzekeres/" + str(BRANCHES[branch]["consumer"]) + ".lean"
        )
        outputs[relative] = branch_consumer_text(source, branch)
        branch_modules.append(module_name(relative))
    pilot_relative = Path(f"{prefix}Pilot.lean")
    outputs[pilot_relative] = import_only_text(branch_modules, public=False)
    if len(outputs) != EXPECTED_PROJECT_MODULES:
        raise ValueError("generated project-module count changed")
    return outputs


def generation_summary(source: dict[str, object]) -> dict[str, object]:
    return {
        "schema_version": 1,
        "task_sha256": EXPECTED_TASK_SHA256,
        "branch_order": list(BRANCH_ORDER),
        "semantic_atoms": 1881,
        "semantic_clauses": len(source["union_ids"]),
        "common_semantic_clauses": len(source["common_ids"]),
        "varying_semantic_clauses": len(source["varying_ids"]),
        "semantic_groups": len(source["group_membership"]),
        "boolean_position_adapters": 2,
        "semantic_helper_blocks": EXPECTED_SHARED["helper_blocks"],
        "project_lean_modules": EXPECTED_PROJECT_MODULES,
        "active_semantic_cap_bytes": MAXIMUM_TOTAL_BYTES,
        "maximum_total_lines": MAXIMUM_TOTAL_LINES,
        "maximum_import_fan_in": IMPORT_FAN_IN,
        "maximum_columns": MAXIMUM_COLUMNS,
        "branches": [
            {
                "name": branch,
                "checkpoint_module": (
                    "ErdosSzekeres."
                    f"{BRANCHES[branch]['stem']}CheckpointLeaf"
                ),
                "checkpoint_declaration": (
                    "synchronizedFiveFanFin11_"
                    f"{BRANCHES[branch]['stem']}_lrat_unsat"
                ),
                "checkpoint_bad": f"{BRANCHES[branch]['stem']}Checkpoint.bad",
                "units": list(BRANCHES[branch]["units"]),
                "variables": BRANCHES[branch]["variables"],
                "semantic_clauses": BRANCHES[branch]["semantic_clauses"],
                "core_clauses": BRANCHES[branch]["core_clauses"],
                "import_width": BRANCHES[branch]["import_width"],
            }
            for branch in BRANCH_ORDER
        ],
        "frozen_hashes": source["frozen_hashes"],
    }


def import_graph(outputs: dict[Path, bytes]) -> dict[str, list[str]]:
    project = {
        module_name(relative): relative
        for relative in outputs
        if relative.parts[0] == "ErdosSzekeres" and relative.suffix == ".lean"
    }
    return {
        module: [item for item in IMPORT_RE.findall(outputs[path].decode()) if item in project]
        for module, path in project.items()
    }


def assert_acyclic(graph: dict[str, list[str]]) -> None:
    state: dict[str, int] = {}

    def visit(node: str) -> None:
        if state.get(node) == 1:
            raise ValueError(f"generated import cycle at {node}")
        if state.get(node) == 2:
            return
        state[node] = 1
        for dependency in graph[node]:
            visit(dependency)
        state[node] = 2

    for node in sorted(graph):
        visit(node)


def validate_outputs(outputs: dict[Path, bytes]) -> None:
    project = [
        path for path in outputs
        if path.parts[0] == "ErdosSzekeres" and path.suffix == ".lean"
    ]
    if len(project) != EXPECTED_PROJECT_MODULES:
        raise ValueError("wrong generated project-module count")
    if len(outputs) != EXPECTED_TOTAL_FILES:
        raise ValueError("wrong generated total-file count")
    total_bytes = sum(len(data) for data in outputs.values())
    total_lines = sum(len(data.decode().splitlines()) for data in outputs.values())
    if total_bytes > MAXIMUM_TOTAL_BYTES:
        raise ValueError("128 MiB active semantic source cap exceeded")
    if total_lines > MAXIMUM_TOTAL_LINES:
        raise ValueError("two-million-line cap exceeded")
    declarations: set[str] = set()
    semantic_clauses: set[str] = set()
    atoms: set[str] = set()
    for relative, data in outputs.items():
        text = data.decode()
        lines = text.splitlines()
        if (
            relative.suffix == ".lean"
            and max((len(line) for line in lines), default=0) > MAXIMUM_COLUMNS
        ):
            raise ValueError(f"100-column limit exceeded: {relative}")
        if relative.parts[0] == "ErdosSzekeres":
            lowered = text.lower()
            for token in FORBIDDEN_TOKENS:
                if token.lower() in lowered:
                    raise ValueError(f"forbidden token {token!r}: {relative}")
            if "SynchronizedFiveFanFin11SemanticAtom" in text:
                raise ValueError(f"legacy semantic atom reference: {relative}")
        imports = IMPORT_RE.findall(text)
        if len(imports) > IMPORT_FAN_IN:
            raise ValueError(f"import fan-in exceeded: {relative}")
        if "Segment" in relative.name and len(data) > MAXIMUM_SEGMENT_BYTES:
            raise ValueError(f"segment/support file too large: {relative}")
        if "SemanticBranch" in relative.name and len(data) > MAXIMUM_BRANCH_BYTES:
            raise ValueError(f"branch consumer too large: {relative}")
        if (
            relative.suffix == ".lean"
            and not DECL_RE.findall(text)
            and len(data) > MAXIMUM_IMPORT_ONLY_BYTES
        ):
            raise ValueError(f"import-only file too large: {relative}")
        for declaration in DECL_RE.findall(text):
            if declaration in declarations:
                raise ValueError(f"duplicate generated declaration: {declaration}")
            declarations.add(declaration)
            if declaration.startswith("SynchronizedFiveFanFin11OriginalAtom"):
                atoms.add(declaration)
            if declaration.startswith(
                "synchronizedFiveFanFin11AltDepth2Semantic_clause"
            ):
                semantic_clauses.add(declaration)
    expected_atoms = {
        original_atom_name(variable) for variable in range(1, 1882)
    }
    if atoms != expected_atoms:
        raise ValueError("stable atom coverage is not exactly 1 through 1881")
    if len(semantic_clauses) != EXPECTED_SHARED["semantic_clause_union"]:
        raise ValueError("semantic theorem coverage count changed")
    assert_acyclic(import_graph(outputs))


def add_run_outputs(
    source: dict[str, object], outputs: dict[Path, bytes]
) -> dict[Path, bytes]:
    summary = generation_summary(source)
    outputs[RUN_REL / "generation-summary.json"] = (
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    ).encode()
    outputs[RUN_REL / "axiom-audit.lean"] = axiom_audit_text()
    manifest_entries = [
        source_metadata(relative, data)
        for relative, data in sorted(outputs.items(), key=lambda item: str(item[0]))
    ]
    manifest = {
        "schema_version": 1,
        "task_sha256": EXPECTED_TASK_SHA256,
        "branch_order": list(BRANCH_ORDER),
        "files_excluding_manifest": manifest_entries,
    }
    outputs[RUN_REL / "source-manifest.json"] = (
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    ).encode()
    return outputs


def generated_outputs(repo: Path) -> dict[Path, bytes]:
    source = semantic_source(repo)
    outputs = generated_project_outputs(source)
    add_run_outputs(source, outputs)
    validate_outputs(outputs)
    return dict(sorted(outputs.items(), key=lambda item: str(item[0])))


def generate(repo: Path, output_root: Path) -> dict[str, str]:
    outputs = generated_outputs(repo)
    for relative, data in outputs.items():
        path = output_root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    return {str(relative): digest(data) for relative, data in outputs.items()}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--output-root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    hashes = generate(args.repo.resolve(), args.output_root.resolve())
    print(json.dumps(hashes, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
