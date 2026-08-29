#!/usr/bin/env python3
"""Generate the frozen Fin11 selected-cube semantic reflection modules."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path


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

PARENT_REL = Path("runs/agents/20260812-frontier-cycle/fin11/core")
LEAF_REL = Path(
    "runs/agents/20260812-promotion-wave/fin11-cubes/depth-6/"
    "v015-1_v111-1_v155-1_v068-0_v142-0_v002-0"
)
RUN_REL = Path("runs/agents/20260820-fin11-semantic-recovery")

PROVENANCE_ONLY_INPUTS = {
    "AGENTS.md": "c13118d6722e1ebe0fa4cea04ce4b1b3053906129d50b05c6f40017fef23ae31",
    "docs/agents/profiles/lean-kernel-engineer.md":
        "04c03faaab5a34725a8b90b2d4b58dce5e24727c8f0eec18ccf98df3ea1791c8",
    "docs/wayfinder/tickets/0051-recover-fin11-semantic-reflection.md":
        "7e5de74dad9c9d3c0638efe85a42fdfe95116c98c33a14f1e45db287cf920016",
    "docs/wayfinder/frontier-portfolio.md":
        "daef9c13e8bbc38353f351c673ab566af19128400cf07a79b1254c41320f7f4e",
}

EXPECTED_INPUTS = {
    "ErdosSzekeres/HalfPureSingletonFan.lean":
        "e2641ed9babfc386b8d369c211be694afef6d95d64529bc373bd9b4cc53797a8",
    "ErdosSzekeres/HalfPureSingletonFanFin10Encoding.lean":
        "d0fa30de2d26bebb77e2de24691548e9e5bd25c2a9b0c3aef086403429ed7751",
    "ErdosSzekeres/HalfPureSingletonFanFin10.lean":
        "ed3a7a369060966bbcd8bdd8bd84e4aed5b6eb8e60129e4414f79d6766d90c66",
    "runs/agents/20260811-four-slot-uniform-round/uniform-fan-n11/model.py":
        "75277e7495e126b3150f3b131564abfe380d07c4877dfb13baba7afb7dfef97c",
    "runs/agents/20260811-four-slot-uniform-round/uniform-fan-n11/generate_cnf.py":
        "ffbf620c9b7d8b8b7ef99fe4eef59e1c9f013af34501b2126d5035930778c12f",
    "runs/agents/20260813-breakout-frontier/fp14/selected-cube.json":
        "63b22cfdb681053d05f6f93b6d51b1dfbf26ed8bdcd308d127051db8d9121f53",
    "runs/agents/20260813-breakout-frontier/fp14/indexed-family-ledger.json":
        "cec2ac6a8475140763e80d9c095db77f30d73fa1355187d16e91e43ab62ee7ef",
    "runs/agents/20260813-breakout-frontier/fp14/build_indexed_family.py":
        "ba77f46b4c9ec0b8f2a131bd982417f020c2e96af4cc266d0c4fd318ae1c37da",
    "runs/agents/20260813-breakout-frontier/fp14/check_indexed_family.py":
        "20909aaed786e7ac2bbdc99c40cd8d45c5957e3c97ea4c924b42b19c52e13399",
    "runs/agents/20260813-breakout-frontier/fp14/audit_selected_cube.py":
        "a64bb83cf85f4bc420c4ec61adbb5f0ee6d7eb7c8045234a784f45172cb06e28",
    str(PARENT_REL / "core.cnf"):
        "50cf18bc1b14ad5c6ded5086a0437e664cdda4411c686f70c55ac6455070ab13",
    str(PARENT_REL / "core-map.json"):
        "afb118f4aecdb2eb831845b9a28ca43588496ef9951fd2aedd6510c890ef7d68",
    str(LEAF_REL / "child.cnf"):
        "9a1b61a1f73bb0e512ec50e7458fd219e472624fe365e37a5b12a88f8370a187",
    str(LEAF_REL / "core/core.cnf"):
        "cbe03200dddabf4e68fdd1669b539ec6fa020cf43070b6460d36ba3ce0d5f714",
    str(LEAF_REL / "core/core.lrat"):
        "5d552f8a9cc6d769da9a2bdcc9e9502e8643967364120087f8f1a50863475f4e",
    str(LEAF_REL / "core/core-map.json"):
        "2dc8b2126adae2e399a32eeba1f3a6851c771cea18411befbc58d438d66e6092",
    "runs/agents/20260820-four-thread-grounding-slate/fin11/manifest.json":
        "bc87d1389c2f5e0447a437ec00843ffbe8b0cd70b604c96bab1563846b5dd4d8",
    "runs/agents/20260820-four-thread-grounding-slate/fin11/result.json":
        "49d19f615e892810a507c8496acce02f0b0aef4096f853e9c8dad06559c26708",
    "ErdosSzekeres/SynchronizedFiveFanFin11CheckpointContext.lean":
        "451edc68d858cc11ace39c4d7c3064e9b36e4a55f43e456499884d922d945dd2",
    "ErdosSzekeres/SynchronizedFiveFanFin11CheckpointSegment031.lean":
        "82a2590ac3c3f38fdec94e7da87b663af9ebf9bed06a3ea68f6aecb493ba1842",
}

EXPECTED_TASK_SHA256 = (
    "ecdc9b8614d8ea67a1f6d9e55137fd6e5b7a4fe9c9d7b10f0a27a957ac926a97"
)
EXPECTED_UNITS = (
    (15, (0, 2, 8), True),
    (111, (3, 4, 6), True),
    (155, (5, 9, 10), True),
    (-68, (1, 5, 7), False),
    (-142, (4, 7, 10), False),
    (-2, (0, 1, 3), False),
)
EXPECTED_FAMILIES = {
    "one_change": 2094,
    "strong_quad_definition": 1993,
    "strong_five_definition": 2047,
    "lower_bad_definition": 809,
    "upper_bad_definition": 698,
    "no_strong_six": 246,
    "no_synchronized_lower": 667,
    "no_synchronized_upper": 621,
}
SUPPORT_SEGMENT_COUNT = 32
CLAUSE_SEGMENT_COUNT = 128


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_frozen_inputs(repo: Path) -> dict[str, bytes]:
    result = {}
    for relative, expected in EXPECTED_INPUTS.items():
        data = (repo / relative).read_bytes()
        if digest(data) != expected:
            raise ValueError(f"frozen input hash mismatch: {relative}")
        result[relative] = data
    task_relative = RUN_REL / "task.json"
    task_data = (repo / task_relative).read_bytes()
    if digest(task_data) != EXPECTED_TASK_SHA256:
        raise ValueError("immutable task hash mismatch")
    result[str(task_relative)] = task_data
    return result


def parse_dimacs(data: bytes) -> tuple[int, tuple[tuple[int, ...], ...]]:
    variables = expected = None
    clauses = []
    pending = []
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
    if variables is None or len(clauses) != expected or pending:
        raise ValueError("bad DIMACS")
    return variables, tuple(clauses)


def quad_triples(quad: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    a, b, c, d = quad
    return ((a, b, c), (a, b, d), (a, c, d), (b, c, d))


def blocker(variables: tuple[int, ...], bits: tuple[bool, ...]) -> tuple[int, ...]:
    return tuple(-var if bit else var for var, bit in zip(variables, bits))


def full_formula() -> tuple[dict[str, object], ...]:
    rows = []

    def add(family: str, index: tuple[object, ...], clause: tuple[int, ...]) -> None:
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
            add("lower_bad_definition", (five,), (-FVAR[five], tvar, LBAD[five]))
        add("upper_bad_definition", (five,), (-UBAD[five], FVAR[five]))
        add(
            "upper_bad_definition",
            (five,),
            (-UBAD[five], *tvars),
        )
        for tvar in tvars:
            add("upper_bad_definition", (five,), (-FVAR[five], -tvar, UBAD[five]))
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
    return tuple(rows)


def semantic_core(repo: Path) -> dict[str, object]:
    frozen = read_frozen_inputs(repo)
    rows = full_formula()
    parent_variables, parent_clauses = parse_dimacs(
        frozen[str(PARENT_REL / "core.cnf")]
    )
    child_variables, child_clauses = parse_dimacs(
        frozen[str(LEAF_REL / "child.cnf")]
    )
    core_variables, core_clauses = parse_dimacs(
        frozen[str(LEAF_REL / "core/core.cnf")]
    )
    parent_map = json.loads(frozen[str(PARENT_REL / "core-map.json")])
    leaf_map = json.loads(frozen[str(LEAF_REL / "core/core-map.json")])
    parent_ids = tuple(parent_map["selected_base_ids"])
    leaf_ids = tuple(leaf_map["selected_base_ids"])
    if (parent_variables, len(parent_clauses)) != (1881, 19207):
        raise ValueError("parent dimensions changed")
    if (child_variables, len(child_clauses)) != (1881, 19213):
        raise ValueError("child dimensions changed")
    if (core_variables, len(core_clauses)) != (1822, 9181):
        raise ValueError("leaf-core dimensions changed")
    reconstructed_parent = tuple(
        rows[semantic_id - 1]["old_clause"] for semantic_id in parent_ids
    )
    if reconstructed_parent != parent_clauses:
        raise ValueError("full semantics does not reconstruct parent core")
    if child_clauses[:19207] != parent_clauses:
        raise ValueError("selected child prefix differs from parent core")
    old_to_new = {
        int(old): int(new)
        for old, new in leaf_map["variable_map_old_to_new"].items()
    }
    new_to_old = {new: old for old, new in old_to_new.items()}
    if tuple(sorted(new_to_old)) != tuple(range(1, 1823)):
        raise ValueError("selected variable map is not dense")

    def remap(clause: tuple[int, ...]) -> tuple[int, ...]:
        return tuple(
            (1 if literal > 0 else -1) * old_to_new[abs(literal)]
            for literal in clause
        )

    entries = []
    units = []
    for core_id, (leaf_id, clause) in enumerate(zip(leaf_ids, core_clauses), 1):
        if remap(child_clauses[leaf_id - 1]) != clause:
            raise ValueError(f"selected remap mismatch at core clause {core_id}")
        if leaf_id <= 19207:
            semantic_id = parent_ids[leaf_id - 1]
            source = rows[semantic_id - 1]
            entry = dict(source)
            entry.update({"core_id": core_id, "leaf_id": leaf_id, "literals": clause})
            entries.append(entry)
        else:
            literal = child_clauses[leaf_id - 1][0]
            units.append({
                "core_id": core_id,
                "leaf_id": leaf_id,
                "literal": literal,
                "literals": clause,
            })
    counts = Counter(entry["family"] for entry in entries)
    if dict(counts) != EXPECTED_FAMILIES or len(entries) != 9175:
        raise ValueError("selected semantic family counts changed")
    original_units = tuple(unit["literal"] for unit in units)
    if original_units != tuple(unit[0] for unit in EXPECTED_UNITS):
        raise ValueError("selected unit order or sign changed")
    for literal, triple, truth in EXPECTED_UNITS:
        if TRIPLES[abs(literal) - 1] != triple or (literal > 0) != truth:
            raise ValueError("selected unit triple adapter changed")
        if abs(literal) not in old_to_new:
            raise ValueError("selected unit variable was dropped")
    all_entries = sorted((*entries, *units), key=lambda entry: entry["core_id"])
    if [entry["core_id"] for entry in all_entries] != list(range(1, 9182)):
        raise ValueError("selected clause order is not dense")
    return {
        "entries": tuple(entries),
        "units": tuple(units),
        "all_entries": tuple(all_entries),
        "new_to_old": new_to_old,
        "old_to_new": old_to_new,
        "frozen_hashes": {
            **PROVENANCE_ONLY_INPUTS,
            **{relative: digest(data) for relative, data in frozen.items()},
        },
    }


def finset(vertices: tuple[int, ...]) -> str:
    return "{" + ", ".join(map(str, vertices)) + "}"


def mask(vertices: tuple[int, ...]) -> int:
    return sum(1 << vertex for vertex in vertices)


def atom_name(variable: int) -> str:
    return f"SynchronizedFiveFanFin11SemanticAtom{variable:04d}"


def atom_term(variable: int) -> str:
    return f"{atom_name(variable)} chi"


def triple_term(triple: tuple[int, ...]) -> str:
    a, b, c = triple
    return f"chi ⟨{a}, {b}, {c}, by decide, by decide⟩"


def strong_quad_term(quad: tuple[int, ...]) -> str:
    a, b, c, d = quad
    return (
        f"SynchronizedFiveFanFin11SemanticStrongQuad chi {a} {b} {c} {d} "
        "(by decide) (by decide) (by decide)"
    )


def public_header(imports: tuple[tuple[str, bool], ...]) -> list[str]:
    lines = ["module", ""]
    for name, public in imports:
        prefix = "public import" if public else "import"
        lines.append(f"{prefix} {name}")
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


def interface_text() -> str:
    lines = public_header((("ErdosSzekeres.HalfPureSingletonFan", True),))
    lines += [
        "/-- The exact selected-cube synchronized five-fan conclusion at Fin 11. -/",
        "def SynchronizedFiveFanFin11Conclusion (chi : TripleColoring 11) : Prop :=",
        "  ∃ side : Finset (Fin 11), ∃ pivot : Fin 11,",
        "    pivot ∉ side ∧",
        "    side.card = 6 ∧",
        "    ((HasDeepBelowSplit chi side {pivot} ∧",
        "        ∀ polygon : Finset (Fin 11),",
        "          polygon ⊆ side → polygon.card = 5 →",
        "            IsStrongPolygonSet chi polygon → IsCupSet chi polygon) ∨",
        "     (HasDeepBelowSplit chi {pivot} side ∧",
        "        ∀ polygon : Finset (Fin 11),",
        "          polygon ⊆ side → polygon.card = 5 →",
        "            IsStrongPolygonSet chi polygon → IsCapSet chi polygon))",
        "",
        "/-- The six original triple literals of the frozen selected Fin11 cube. -/",
        "def SynchronizedFiveFanFin11SelectedCube (chi : TripleColoring 11) : Prop :=",
        f"  {triple_term((0, 2, 8))} = Turn.left ∧",
        f"    {triple_term((3, 4, 6))} = Turn.left ∧",
        f"    {triple_term((5, 9, 10))} = Turn.left ∧",
        f"    {triple_term((1, 5, 7))} = Turn.right ∧",
        f"    {triple_term((4, 7, 10))} = Turn.right ∧",
        f"    {triple_term((0, 1, 3))} = Turn.right",
        "",
        "end ErdosSzekeres",
        "",
        "end",
        "",
    ]
    return "\n".join(lines)


def strong_set_iff_lines(vertices: tuple[int, ...]) -> list[str]:
    theorem = f"synchronizedFiveFanFin11_strongSet_iff_mask{mask(vertices):04d}"
    quads = tuple(itertools.combinations(vertices, 4))
    lines = [
        f"theorem {theorem} (chi : TripleColoring 11) :",
        f"    IsStrongPolygonSet chi {finset(vertices)} ↔",
    ]
    for index, quad in enumerate(quads):
        a, b, c, d = quad
        suffix = " ∧" if index + 1 < len(quads) else " := by"
        lines += [
            f"      SynchronizedFiveFanFin11SemanticStrongQuad chi {a} {b} {c} {d}",
            f"        (by decide) (by decide) (by decide){suffix}",
        ]
    lines += ["  constructor", "  · intro h", "    refine ⟨"]
    for index, quad in enumerate(quads):
        a, b, c, d = quad
        suffix = "," if index + 1 < len(quads) else "⟩"
        lines += [
            "      (by",
            "        simpa [SynchronizedFiveFanFin11SemanticStrongQuad] using h",
            f"          (i := {a}) (j := {b}) (k := {c}) (l := {d})",
            "          (by decide) (by decide) (by decide)",
            f"          (by simp) (by simp) (by simp) (by simp)){suffix}",
        ]
    facts = ", ".join(f"h{index}" for index in range(len(quads)))
    choices = " | ".join("rfl" for _ in vertices)
    lines += [
        f"  · rintro ⟨{facts}⟩ i j k l hij hjk hkl hi hj hk hl",
        "    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl",
        f"    rcases hi with {choices} <;>",
        f"      rcases hj with {choices} <;>",
        f"      rcases hk with {choices} <;>",
        f"      rcases hl with {choices} <;> try omega",
        "    all_goals simp_all [SynchronizedFiveFanFin11SemanticStrongQuad]",
        "",
    ]
    return lines


def pure_set_iff_lines(five: tuple[int, ...], cup: bool) -> list[str]:
    kind = "cup" if cup else "cap"
    predicate = "IsCupSet" if cup else "IsCapSet"
    turn = "left" if cup else "right"
    theorem = f"synchronizedFiveFanFin11_{kind}Set_iff_mask{mask(five):04d}"
    triples = tuple(itertools.combinations(five, 3))
    lines = [
        f"theorem {theorem} (chi : TripleColoring 11) :",
        f"    {predicate} chi {finset(five)} ↔",
    ]
    for index, triple in enumerate(triples):
        suffix = " ∧" if index + 1 < len(triples) else " := by"
        lines.append(f"      {triple_term(triple)} = Turn.{turn}{suffix}")
    lines += ["  constructor", "  · intro h", "    exact ⟨"]
    for index in range(len(triples)):
        suffix = "," if index + 1 < len(triples) else "⟩"
        lines.append(f"      h _ (by simp) (by simp) (by simp){suffix}")
    facts = ", ".join(f"h{index}" for index in range(len(triples)))
    choices = " | ".join("rfl" for _ in five)
    lines += [
        f"  · rintro ⟨{facts}⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk",
        "    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk",
        f"    rcases hi with {choices} <;>",
        f"      rcases hj with {choices} <;>",
        f"      rcases hk with {choices} <;> try omega",
        "",
    ]
    return lines


def five_subset_lines(side: tuple[int, ...]) -> list[str]:
    theorem = f"synchronizedFiveFanFin11_fiveSubset_mask{mask(side):04d}"
    fives = tuple(itertools.combinations(side, 5))
    lines = [
        f"theorem {theorem} :",
        f"    ∀ polygon : Finset (Fin 11), polygon ⊆ {finset(side)} →",
        "      polygon.card = 5 →",
    ]
    for index, five in enumerate(fives):
        prefix = "        " if index == 0 else "          "
        suffix = " ∨" if index + 1 < len(fives) else " := by decide"
        lines.append(f"{prefix}polygon = {finset(five)}{suffix}")
    lines.append("")
    return lines


def encoding_text(core: dict[str, object]) -> str:
    lines = public_header(
        (("ErdosSzekeres.SynchronizedFiveFanFin11SemanticInterface", True),)
    )
    lines += [
        "def SynchronizedFiveFanFin11SemanticStrongQuad",
        "    (chi : TripleColoring 11) (a b c d : Fin 11)",
        "    (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=",
        "  chi ⟨a, b, c, hab, hbc⟩ = chi ⟨a, b, d, hab, hbc.trans hcd⟩ ∧",
        "    chi ⟨a, c, d, hab.trans hbc, hcd⟩ = chi ⟨b, c, d, hbc, hcd⟩",
        "",
    ]
    new_to_old = core["new_to_old"]
    for variable in range(1, 1823):
        old = new_to_old[variable]
        lines.append(f"def {atom_name(variable)} (chi : TripleColoring 11) : Prop :=")
        if old <= 165:
            lines.append(f"  {triple_term(TRIPLES[old - 1])} = Turn.left")
        elif old <= 495:
            lines.append(f"  {strong_quad_term(QUADS[old - 166])}")
        elif old <= 957:
            lines.append(f"  IsStrongPolygonSet chi {finset(FIVES[old - 496])}")
        elif old <= 1419:
            five = FIVES[old - 958]
            lines += [
                f"  IsStrongPolygonSet chi {finset(five)} ∧",
                f"    ¬IsCupSet chi {finset(five)}",
            ]
        else:
            five = FIVES[old - 1420]
            lines += [
                f"  IsStrongPolygonSet chi {finset(five)} ∧",
                f"    ¬IsCapSet chi {finset(five)}",
            ]
        lines.append("")
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def semantic_helper_blocks(
    core: dict[str, object],
) -> tuple[tuple[str, ...], ...]:
    strong_fives: set[tuple[int, ...]] = set()
    cup_fives: set[tuple[int, ...]] = set()
    cap_fives: set[tuple[int, ...]] = set()
    branch_sides: set[tuple[int, ...]] = set()
    for entry in core["entries"]:
        family = entry["family"]
        index = entry["index"]
        if family in {
            "strong_five_definition",
            "lower_bad_definition",
            "upper_bad_definition",
        }:
            strong_fives.add(index[0])
        if family == "no_strong_six":
            strong_fives.update(itertools.combinations(index[0], 5))
        if family == "lower_bad_definition":
            cup_fives.add(index[0])
        if family == "upper_bad_definition":
            cap_fives.add(index[0])
        if family.startswith("no_synchronized_"):
            branch_sides.add(index[0])
    blocks = []
    for five in sorted(strong_fives):
        blocks.append(tuple(strong_set_iff_lines(five)))
    for five in sorted(cup_fives):
        blocks.append(tuple(pure_set_iff_lines(five, True)))
    for five in sorted(cap_fives):
        blocks.append(tuple(pure_set_iff_lines(five, False)))
    for side in sorted(branch_sides):
        blocks.append(tuple(five_subset_lines(side)))
    return tuple(blocks)


def balanced_helper_segments(
    blocks: tuple[tuple[str, ...], ...],
) -> tuple[tuple[tuple[str, ...], ...], ...]:
    chunks = [[] for _ in range(SUPPORT_SEGMENT_COUNT)]
    weights = [0] * SUPPORT_SEGMENT_COUNT
    for block in blocks:
        index = min(
            range(SUPPORT_SEGMENT_COUNT),
            key=lambda item: (weights[item], item),
        )
        chunks[index].append(block)
        weights[index] += sum(len(line) + 1 for line in block)
    if any(not chunk for chunk in chunks):
        raise ValueError("empty semantic helper segment")
    return tuple(tuple(chunk) for chunk in chunks)


def support_segment_text(
    index: int,
    blocks: tuple[tuple[str, ...], ...],
) -> str:
    dependency = (
        "ErdosSzekeres.SynchronizedFiveFanFin11SemanticEncoding"
        if index == 0
        else (
            "ErdosSzekeres."
            f"SynchronizedFiveFanFin11SemanticSupportSegment{index - 1:03d}"
        )
    )
    lines = public_header(
        ((dependency, True),)
    )
    lines += [
        f"/-! Semantic helper facts in bounded group {index:03d}. -/",
        "",
    ]
    for block in blocks:
        lines += list(block)
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def support_text() -> str:
    imports = (
        (
            "ErdosSzekeres."
            "SynchronizedFiveFanFin11SemanticSupportSegment"
            f"{SUPPORT_SEGMENT_COUNT - 1:03d}",
            True,
        ),
    )
    lines = public_header(imports)
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def failure_lines(literals: tuple[int, ...]) -> list[str]:
    lines = ["    ¬("]
    for index, literal in enumerate(literals):
        term = atom_term(abs(literal))
        proposition = f"¬{term}" if literal > 0 else term
        suffix = " ∧" if index + 1 < len(literals) else ") := by"
        lines.append(f"      {proposition}{suffix}")
    return lines


def unfold_at(lines: list[str], literals: tuple[int, ...], target: str) -> None:
    for variable in sorted({abs(literal) for literal in literals}):
        lines.append(f"  unfold {atom_name(variable)} at {target}")


def color_cases(quad: tuple[int, ...]) -> list[str]:
    lines = []
    for index, triple in enumerate(quad_triples(quad)):
        indent = "  " + "  " * index
        lines.append(f"{indent}cases hcolor{index} : {triple_term(triple)} <;>")
    lines.append("          simp_all [TurnSequenceAllowed]")
    return lines


def semantic_clause_lines(entry: dict[str, object]) -> list[str]:
    clause_id = entry["core_id"]
    family = entry["family"]
    index = entry["index"]
    literals = entry["literals"]
    theorem = f"synchronizedFiveFanFin11Semantic_clause{clause_id:05d}"
    lines = [f"theorem {theorem} (chi : TripleColoring 11)"]
    if family == "one_change":
        a, b, c, d = index[0]
        lines += ["    (hone : OneChangeOn chi Finset.univ) :"]
        lines += failure_lines(literals)
        lines += [
            "  intro hbad",
            f"  have hallowed := hone (i := {a}) (j := {b}) (k := {c}) (l := {d})",
            "    (by decide) (by decide) (by decide)",
            "    (by simp) (by simp) (by simp) (by simp)",
        ]
        unfold_at(lines, literals, "hbad")
        lines += color_cases(index[0])
    elif family == "strong_quad_definition":
        lines += ["    :"] + failure_lines(literals)
        lines.append("  intro hbad")
        unfold_at(lines, literals, "hbad")
        lines += color_cases(index[0])
        lines[-1] = (
            "          simp_all "
            "[TurnSequenceAllowed, SynchronizedFiveFanFin11SemanticStrongQuad]"
        )
    elif family in {
        "strong_five_definition",
        "lower_bad_definition",
        "upper_bad_definition",
    }:
        five = index[0]
        lines += ["    :"] + failure_lines(literals)
        lines.append("  intro hbad")
        unfold_at(lines, literals, "hbad")
        if family == "strong_five_definition":
            strong_name = (
                f"synchronizedFiveFanFin11_strongSet_iff_mask{mask(five):04d}"
            )
            lines += ["  simp only [", f"    {strong_name},", "  ] at hbad"]
            lines.append("  tauto")
            return lines
        if len(literals) == 2:
            lines.append("  exact hbad.2 hbad.1.1")
            return lines
        lower = family == "lower_bad_definition"
        pure_kind = "cup" if lower else "cap"
        pure_name = (
            f"synchronizedFiveFanFin11_{pure_kind}Set_iff_mask{mask(five):04d}"
        )
        triples = tuple(itertools.combinations(five, 3))
        fact_names = [f"h{item}" for item in range(len(triples))]
        if len(literals) == 11:
            lines += [
                "  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,",
                f"    {', '.join(fact_names)}⟩",
                "  apply hnotPure",
                f"  apply ({pure_name} chi).mpr",
            ]
            if lower:
                lines.append(f"  exact ⟨{', '.join(fact_names)}⟩")
            else:
                for color_index, triple in enumerate(triples):
                    term = triple_term(triple)
                    lines += [
                        f"  have hright{color_index} : {term} = Turn.right := by",
                        f"    cases hcolor : {term} <;> simp_all",
                    ]
                right_names = [
                    f"hright{item}" for item in range(len(triples))
                ]
                lines.append(f"  exact ⟨{', '.join(right_names)}⟩")
            return lines
        if len(literals) == 3:
            triple_variable = abs(literals[1])
            color_index = next(
                item
                for item, triple in enumerate(triples)
                if TVAR[triple] == triple_variable
            )
            lines += [
                "  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩",
                "  apply hnotBad",
                "  refine ⟨hstrong, ?_⟩",
                "  intro hpure",
                f"  have hcolors := ({pure_name} chi).mp hpure",
                f"  rcases hcolors with ⟨{', '.join(fact_names)}⟩",
            ]
            if lower:
                lines.append(f"  exact hcolor h{color_index}")
            else:
                lines.append(
                    f"  exact Turn.noConfusion (hcolor.symm.trans h{color_index})"
                )
            return lines
        raise ValueError(f"bad pure-definition clause {clause_id}")
    elif family == "no_strong_six":
        six = index[0]
        quads = tuple(itertools.combinations(six, 4))
        quad_fact = {quad: f"hq{item}" for item, quad in enumerate(quads)}
        qfacts = [quad_fact[quad] for quad in quads]
        fives = [tuple(vertex for vertex in six if vertex != excluded)
                 for excluded in six]
        lines += ["    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6) :"]
        lines += failure_lines(literals)
        lines.append("  intro hbad")
        unfold_at(lines, literals, "hbad")
        lines.append(f"  rcases hbad with ⟨{', '.join(qfacts)}⟩")
        for item, five in enumerate(fives):
            facts = [quad_fact[quad] for quad in itertools.combinations(five, 4)]
            strong_name = (
                f"synchronizedFiveFanFin11_strongSet_iff_mask{mask(five):04d}"
            )
            lines += [
                f"  have hfive{item} : IsStrongPolygonSet chi {finset(five)} := by",
                f"    apply ({strong_name} chi).mpr",
                f"    exact ⟨{', '.join(facts)}⟩",
            ]
        lines += [
            "  apply hnoStrong",
            f"  refine ⟨{finset(six)}, by simp, by decide, ?_⟩",
            "  intro i j k l hij hjk hkl hi hj hk hl",
            "  let t : Finset (Fin 11) := {i, j, k, l}",
            "  have htcard : t.card = 4 := by",
            "    simp [t, ne_of_lt hij, ne_of_lt hjk, ne_of_lt hkl,",
            "      ne_of_lt (hij.trans hjk), ne_of_lt (hjk.trans hkl),",
            "      ne_of_lt (hij.trans (hjk.trans hkl))]",
            f"  have hcardlt : t.card < ({finset(six)} : Finset (Fin 11)).card := by",
            "    rw [htcard]",
            "    decide",
            "  obtain ⟨x, hxs, hxt⟩ :=",
            "    Finset.exists_mem_notMem_of_card_lt_card hcardlt",
            "  have hmem (y : Fin 11) (hyt : y ∈ t)",
            f"      (hy : y ∈ ({finset(six)} : Finset (Fin 11))) :",
            f"      y ∈ ({finset(six)} : Finset (Fin 11)).erase x := by",
            "    exact Finset.mem_erase.mpr ⟨fun hyx => hxt (hyx ▸ hyt), hy⟩",
            "  simp only [Finset.mem_insert, Finset.mem_singleton] at hxs",
            f"  rcases hxs with {' | '.join('rfl' for _ in six)}",
        ]
        for item in range(len(six)):
            five = fives[item]
            excluded = six[item]
            lines += [
                "  · have herase :",
                f"        ({finset(six)} : Finset (Fin 11)).erase {excluded} =",
                f"          {finset(five)} := by decide",
                f"    exact hfive{item} hij hjk hkl",
                "      (herase ▸ hmem i (by simp [t]) hi)",
                "      (herase ▸ hmem j (by simp [t]) hj)",
                "      (herase ▸ hmem k (by simp [t]) hk)",
                "      (herase ▸ hmem l (by simp [t]) hl)",
            ]
    else:
        side, pivot = index
        lower = family == "no_synchronized_lower"
        if len(side) != 6 or len(literals) != 21:
            raise ValueError(f"branch clause {clause_id} has changed shape")
        branch = "Or.inl" if lower else "Or.inr"
        pure = "IsCupSet" if lower else "IsCapSet"
        union = tuple(sorted((*side, pivot)))
        choices = " | ".join("rfl" for _ in union)
        lines += [
            "    (hno : ¬SynchronizedFiveFanFin11Conclusion chi) :",
        ]
        lines += failure_lines(literals)
        fact_names = [f"h{item}" for item in range(21)]
        lines += [
            f"  rintro ⟨{', '.join(fact_names[:11])},",
            f"    {', '.join(fact_names[11:])}⟩",
        ]
        for item, literal in enumerate(literals):
            lines.append(f"  unfold {atom_name(abs(literal))} at h{item}")
        if any(literal > 0 for literal in literals[:15]):
            lines += [
                "  have right_of_not_left (t : OrderedTriple 11)",
                "      (ht : ¬chi t = Turn.left) : chi t = Turn.right := by",
                "    cases hcolor : chi t",
                "    · exact (ht hcolor).elim",
                "    · rfl",
            ]
        crossing_tactics = [
            (f"      | exact h{item}" if literal < 0 else
             f"      | exact right_of_not_left _ h{item}")
            for item, literal in enumerate(literals[:15])
        ]
        lines += [
            "  apply hno",
            "  unfold SynchronizedFiveFanFin11Conclusion",
            f"  refine ⟨{finset(side)}, {pivot}, by decide, by decide, {branch} ?_⟩",
            "  refine ⟨?_, ?_⟩",
            "  · refine ⟨by decide, ?_⟩",
            "    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk hnotLower hnotUpper",
            "    simp only [Finset.mem_insert, Finset.mem_singleton,",
            "      Finset.mem_union, or_assoc] at hi hj hk",
            f"    rcases hi with {choices} <;>",
            f"      rcases hj with {choices} <;>",
            f"      rcases hk with {choices} <;> try omega",
            "    all_goals",
            "      simp at hnotLower hnotUpper ⊢",
            "    all_goals first",
            *crossing_tactics,
            "  · intro polygon hsub hcard hstrong",
            f"    have heq := synchronizedFiveFanFin11_fiveSubset_mask{mask(side):04d}",
            "      polygon hsub hcard",
        ]
        lines.append("    rcases heq with heq | heq | heq | heq | heq | heq")
        for subset_index, five in enumerate(itertools.combinations(side, 5)):
            bad_fact = 15 + subset_index
            lines += [
                f"    · subst polygon",
                f"      show {pure} chi {finset(five)}",
                "      by_contra hnotPure",
                f"      apply h{bad_fact}",
                "      exact ⟨hstrong, hnotPure⟩",
            ]
    return lines


def unit_clause_lines(
    entry: dict[str, object],
    old_to_new: dict[int, int],
) -> list[str]:
    clause_id = entry["core_id"]
    literal = entry["literal"]
    new_literal = (1 if literal > 0 else -1) * old_to_new[abs(literal)]
    if entry["literals"] != (new_literal,):
        raise ValueError(f"unit remap changed at core clause {clause_id}")
    theorem = f"synchronizedFiveFanFin11Semantic_clause{clause_id:05d}"
    lines = [
        f"theorem {theorem} (chi : TripleColoring 11)",
        "    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :",
    ]
    lines += failure_lines((new_literal,))
    lines += [
        "  unfold SynchronizedFiveFanFin11SelectedCube at hcube",
        f"  unfold {atom_name(abs(new_literal))}",
        "  rcases hcube with ⟨h0, h1, h2, h3, h4, h5⟩",
        "  simp_all",
    ]
    return lines


def segment_text(
    index: int,
    entries: tuple[dict[str, object], ...],
    old_to_new: dict[int, int],
) -> str:
    dependency = (
        "ErdosSzekeres.SynchronizedFiveFanFin11SemanticSupport"
        if index == 0
        else f"ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment{index - 1:03d}"
    )
    lines = public_header(
        ((dependency, True),)
    )
    lines += [
        f"/-! Exact selected-core semantic clauses in bounded group {index:03d}. -/",
        "",
    ]
    for entry in entries:
        if "family" in entry:
            lines += semantic_clause_lines(entry)
        else:
            lines += unit_clause_lines(entry, old_to_new)
        lines.append("")
    lines += ["end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def balanced_segments(
    entries: tuple[dict[str, object], ...],
) -> tuple[tuple[dict[str, object], ...], ...]:
    quotient, remainder = divmod(len(entries), CLAUSE_SEGMENT_COUNT)
    chunks = []
    start = 0
    for index in range(CLAUSE_SEGMENT_COUNT):
        size = quotient + (1 if index < remainder else 0)
        chunks.append(entries[start:start + size])
        start += size
    if start != len(entries) or any(not chunk for chunk in chunks):
        raise ValueError("bad semantic segment partition")
    return tuple(chunks)


def semantic_clause_application(entry: dict[str, object]) -> str:
    application = f"synchronizedFiveFanFin11Semantic_clause{entry['core_id']:05d} chi"
    family = str(entry.get("family", ""))
    if family == "one_change":
        application += " hone"
    elif family == "no_strong_six":
        application += " hnoStrong"
    elif family.startswith("no_synchronized_"):
        application += " hno"
    elif "family" not in entry:
        application += " hcube"
    return application


def append_or_refutation(
    lines: list[str],
    entries: tuple[dict[str, object], ...],
    start: int,
    stop: int,
    hypothesis: str,
    indent: str,
) -> None:
    if stop - start == 1:
        lines.append(f"{indent}exact {semantic_clause_application(entries[start])}")
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


def final_text(core: dict[str, object]) -> str:
    imports = [
        ("ErdosSzekeres.SynchronizedFiveFanFin11SemanticInterface", True),
        ("ErdosSzekeres.SynchronizedFiveFanFin11CheckpointSegment031", False),
        (
            "ErdosSzekeres."
            f"SynchronizedFiveFanFin11SemanticSegment{CLAUSE_SEGMENT_COUNT - 1:03d}",
            False,
        ),
    ]
    lines = public_header(tuple(imports))
    lines += [
        "set_option maxHeartbeats 100000000",
        "",
        "/-- The frozen Fin11 cube forces its exact synchronized five-fan conclusion. -/",
        "theorem synchronizedFiveFanSideAtSixFinEleven_of_selectedCube",
        "    (chi : TripleColoring 11)",
        "    (hone : OneChangeOn chi Finset.univ)",
        "    (hnoStrong : ¬ContainsStrongPolygonSet chi Finset.univ 6)",
        "    (hcube : SynchronizedFiveFanFin11SelectedCube chi) :",
        "    SynchronizedFiveFanFin11Conclusion chi := by",
        "  by_contra hno",
        "  have hbad :=",
        "    synchronizedFiveFanFin11_indexedCubeLeaf_lrat_unsat",
    ]
    for variable in range(1, 1823):
        lines.append(f"      ({atom_term(variable)})")
    lines.append("  unfold SynchronizedFiveFanFin11Checkpoint.bad at hbad")
    entries = tuple(core["all_entries"])
    append_or_refutation(lines, entries, 0, len(entries), "hbad", "  ")
    lines += ["", "end ErdosSzekeres", "", "end", ""]
    return "\n".join(lines)


def axiom_audit_text() -> str:
    return "\n".join([
        "import ErdosSzekeres.SynchronizedFiveFanFin11SemanticReflection",
        "",
        "#print axioms ErdosSzekeres.SynchronizedFiveFanFin11Conclusion",
        "#print axioms ErdosSzekeres.SynchronizedFiveFanFin11SelectedCube",
        "#print axioms",
        "  ErdosSzekeres.synchronizedFiveFanSideAtSixFinEleven_of_selectedCube",
        "",
    ])


def generated_outputs(repo: Path) -> dict[Path, bytes]:
    core = semantic_core(repo)
    chunks = balanced_segments(core["all_entries"])
    helper_chunks = balanced_helper_segments(semantic_helper_blocks(core))
    outputs = {
        Path("ErdosSzekeres/SynchronizedFiveFanFin11SemanticInterface.lean"):
            interface_text().encode(),
        Path("ErdosSzekeres/SynchronizedFiveFanFin11SemanticEncoding.lean"):
            encoding_text(core).encode(),
        Path("ErdosSzekeres/SynchronizedFiveFanFin11SemanticSupport.lean"):
            support_text().encode(),
        Path("ErdosSzekeres/SynchronizedFiveFanFin11SemanticReflection.lean"):
            final_text(core).encode(),
        RUN_REL / "axiom-audit.lean": axiom_audit_text().encode(),
    }
    for index, chunk in enumerate(helper_chunks):
        relative = Path(
            "ErdosSzekeres/"
            f"SynchronizedFiveFanFin11SemanticSupportSegment{index:03d}.lean"
        )
        outputs[relative] = support_segment_text(index, chunk).encode()
    for index, chunk in enumerate(chunks):
        relative = Path(
            f"ErdosSzekeres/SynchronizedFiveFanFin11SemanticSegment{index:03d}.lean"
        )
        outputs[relative] = segment_text(index, chunk, core["old_to_new"]).encode()
    summary = {
        "schema_version": 1,
        "task_sha256": EXPECTED_TASK_SHA256,
        "semantic_variables": 1822,
        "semantic_clauses": 9175,
        "cube_units": 6,
        "core_clauses": 9181,
        "support_segment_count": SUPPORT_SEGMENT_COUNT,
        "clause_segment_count": CLAUSE_SEGMENT_COUNT,
        "segment_sizes": [len(chunk) for chunk in chunks],
        "support_segment_sizes": [len(chunk) for chunk in helper_chunks],
        "family_counts": EXPECTED_FAMILIES,
        "unit_literals": [unit[0] for unit in EXPECTED_UNITS],
        "frozen_hashes": core["frozen_hashes"],
    }
    outputs[RUN_REL / "generation-summary.json"] = (
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    ).encode()
    return outputs


def generate(repo: Path, output_root: Path) -> dict[str, str]:
    outputs = generated_outputs(repo)
    for relative, data in outputs.items():
        path = output_root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    return {
        str(relative): digest(data)
        for relative, data in sorted(outputs.items(), key=lambda item: str(item[0]))
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--output-root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    hashes = generate(args.repo.resolve(), args.output_root.resolve())
    print(json.dumps(hashes, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
