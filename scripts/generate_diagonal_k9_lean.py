#!/usr/bin/env python3
"""Generate the semantic Lean bridge for the two dense k=9 cup-block cores.

The LRAT theorems prove only that their dense propositional CNFs are
inconsistent.  This generator reconstructs the source clause attached to each
retained clause, checks the dense variable renaming, and emits explicit Lean
proofs that every retained clause follows from the normalized geometric
predicates.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator


N = 15
CAP = 4
CUP = 9
STRONG = 9
PREFIX = "DiagonalCupBlocksK9"


@dataclass(frozen=True)
class Orientation:
    tag: str
    left: int
    right: int
    source_stem: str
    expected_cnf_sha256: str
    expected_lrat_sha256: str
    expected_variables: int
    expected_clauses: int
    expected_additions: int
    expected_families: dict[str, int]
    chunks: int


ORIENTATIONS = (
    Orientation(
        tag="78",
        left=7,
        right=8,
        source_stem="k9-78",
        expected_cnf_sha256="ed5d3604a251013d80716f2cff0f0d7eb34a81936bcf281792f39b56a839fe72",
        expected_lrat_sha256="47654921221546d883544620525cb98806238d65f112467f9ccfe10dfafa0c8a",
        expected_variables=396,
        expected_clauses=1157,
        expected_additions=812,
        expected_families={"quad": 1016, "cap": 26, "cup": 15, "strong": 9, "unit": 91},
        chunks=16,
    ),
    Orientation(
        tag="87",
        left=8,
        right=7,
        source_stem="k9-87",
        expected_cnf_sha256="21c281818b3688488debe1d521b6f4b468c2d34a2d79db8a3a7962a7ab679d39",
        expected_lrat_sha256="150596401f45f9789deaba920e0e87690eceb5c68ad8524e2ac7611bd3544091",
        expected_variables=280,
        expected_clauses=429,
        expected_additions=239,
        expected_families={"quad": 322, "cap": 8, "cup": 5, "strong": 3, "unit": 91},
        chunks=8,
    ),
)


@dataclass(frozen=True)
class Origin:
    kind: str
    vertices: tuple[int, ...]
    values: tuple[bool, ...]
    side: str = ""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_if_changed(path: Path, content: str | bytes) -> None:
    payload = content.encode() if isinstance(content, str) else content
    if path.exists() and path.read_bytes() == payload:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_bytes(payload)
    os.replace(temporary, path)


def triples(vertices) -> tuple[tuple[int, int, int], ...]:
    return tuple(itertools.combinations(vertices, 3))


ALL_TRIPLES = triples(range(N))
VARIABLES = {triple: index + 1 for index, triple in enumerate(ALL_TRIPLES)}


def forbidden_assignment(
    keys: tuple[tuple[int, int, int], ...], values: tuple[bool, ...]
) -> tuple[int, ...]:
    return tuple(-VARIABLES[key] if value else VARIABLES[key] for key, value in zip(keys, values))


def strong_patterns(size: int) -> tuple[tuple[bool, ...], ...]:
    local = triples(range(size))
    positions = {triple: index for index, triple in enumerate(local)}
    parent = list(range(len(local)))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> None:
        x, y = find(x), find(y)
        if x != y:
            parent[y] = x

    for i, j, k, l in itertools.combinations(range(size), 4):
        union(positions[i, j, k], positions[i, j, l])
        union(positions[i, k, l], positions[j, k, l])
    roots = sorted({find(index) for index in range(len(local))})
    components = {root: index for index, root in enumerate(roots)}
    return tuple(
        tuple(assignment[components[find(index)]] for index in range(len(local)))
        for assignment in itertools.product((False, True), repeat=len(roots))
    )


STRONG_PATTERNS = strong_patterns(STRONG)


def source_clauses(orientation: Orientation) -> Iterator[tuple[tuple[int, ...], Origin]]:
    for vertices in itertools.combinations(range(N), 4):
        i, j, k, l = vertices
        keys = ((i, j, k), (i, j, l), (i, k, l), (j, k, l))
        for values in itertools.product((False, True), repeat=4):
            if sum(x != y for x, y in zip(values, values[1:])) > 1:
                values_tuple = tuple(values)
                yield forbidden_assignment(keys, values_tuple), Origin("quad", vertices, values_tuple)
    for vertices in itertools.combinations(range(N), CAP):
        keys = triples(vertices)
        values = tuple(False for _ in keys)
        yield tuple(VARIABLES[key] for key in keys), Origin("cap", vertices, values)
    for vertices in itertools.combinations(range(N), CUP):
        keys = triples(vertices)
        values = tuple(True for _ in keys)
        yield tuple(-VARIABLES[key] for key in keys), Origin("cup", vertices, values)
    local = triples(range(STRONG))
    for vertices in itertools.combinations(range(N), STRONG):
        keys = tuple(tuple(vertices[index] for index in triple) for triple in local)
        for values in STRONG_PATTERNS:
            yield forbidden_assignment(keys, values), Origin("strong", vertices, values)
    for side, block in (
        ("left", range(orientation.left)),
        ("right", range(orientation.left, N)),
    ):
        for triple in triples(block):
            yield (VARIABLES[triple],), Origin("unit", triple, (True,), side)


def parse_dimacs(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = None
    declared = None
    clauses: list[tuple[int, ...]] = []
    current: list[int] = []
    for line_number, text in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        text = text.strip()
        if not text or text.startswith("c"):
            continue
        if text.startswith("p"):
            fields = text.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"] or variables is not None:
                raise ValueError(f"{path}:{line_number}: malformed CNF header")
            variables, declared = int(fields[2]), int(fields[3])
            continue
        if variables is None:
            raise ValueError(f"{path}:{line_number}: clause before header")
        for field in text.split():
            literal = int(field)
            if literal == 0:
                clauses.append(tuple(current))
                current = []
            else:
                if abs(literal) > variables:
                    raise ValueError(f"{path}:{line_number}: literal out of range")
                current.append(literal)
    if variables is None or declared is None or current or len(clauses) != declared:
        raise ValueError(f"{path}: inconsistent CNF")
    return variables, clauses


def retained_clauses(
    run_dir: Path, orientation: Orientation
) -> tuple[list[int], list[tuple[int, ...]], list[Origin]]:
    map_path = run_dir / f"{orientation.source_stem}-dense-variable-map.json"
    core_path = run_dir / f"{orientation.source_stem}-core-map.json"
    dense_path = run_dir / f"{orientation.source_stem}-dense-core.cnf"
    dense_map = json.loads(map_path.read_text())
    core_map = json.loads(core_path.read_text())
    old_variables = list(dense_map["old_variable_ids"])
    dense_variables, dense_clauses = parse_dimacs(dense_path)
    old_clause_ids = list(core_map["old_original_clause_ids"])
    if dense_variables != len(old_variables) or dense_variables != orientation.expected_variables:
        raise ValueError(f"{orientation.tag}: dense variable map mismatch")
    if len(dense_clauses) != len(old_clause_ids) or len(dense_clauses) != orientation.expected_clauses:
        raise ValueError(f"{orientation.tag}: dense clause map mismatch")
    wanted = set(old_clause_ids)
    found: dict[int, tuple[tuple[int, ...], Origin]] = {}
    for clause_id, item in enumerate(source_clauses(orientation), 1):
        if clause_id in wanted:
            found[clause_id] = item
    if found.keys() != wanted:
        raise ValueError(f"{orientation.tag}: missing retained source clauses")
    origins: list[Origin] = []
    for dense_clause, old_clause_id in zip(dense_clauses, old_clause_ids):
        old_clause = tuple(
            (1 if literal > 0 else -1) * old_variables[abs(literal) - 1]
            for literal in dense_clause
        )
        expected_clause, origin = found[old_clause_id]
        if old_clause != expected_clause:
            raise ValueError(f"{orientation.tag}: dense/source mismatch at clause {old_clause_id}")
        origins.append(origin)
    counts = {kind: sum(origin.kind == kind for origin in origins) for kind in orientation.expected_families}
    if counts != orientation.expected_families:
        raise ValueError(f"{orientation.tag}: retained family counts differ: {counts}")
    return old_variables, dense_clauses, origins


def balanced_join(items: list[str], operator: str) -> str:
    if len(items) == 1:
        return items[0]
    midpoint = len(items) // 2
    return f"({balanced_join(items[:midpoint], operator)} {operator} {balanced_join(items[midpoint:], operator)})"


def balanced_not_or_proof(items: list[str]) -> str:
    if len(items) == 1:
        return items[0]
    midpoint = len(items) // 2
    return (
        "(fun h ↦ Or.elim h "
        + balanced_not_or_proof(items[:midpoint])
        + " "
        + balanced_not_or_proof(items[midpoint:])
        + ")"
    )


def balanced_chunks(items: list[str], count: int) -> list[list[str]]:
    if count == 1:
        return [items]
    if count <= 0 or count > len(items) or count % 2:
        raise ValueError("chunk count must form an even binary split tree")
    midpoint = len(items) // 2
    return balanced_chunks(items[:midpoint], count // 2) + balanced_chunks(items[midpoint:], count // 2)


def turn_term(bit: bool) -> str:
    return "Turn.left" if bit else "Turn.right"


def triple_prop(old_variable: int) -> str:
    i, j, k = ALL_TRIPLES[old_variable - 1]
    return f"(χ ⟨{i}, {j}, {k}, by decide, by decide⟩ = Turn.left)"


def selected_triple_term(size: int, triple: tuple[int, int, int]) -> str:
    i, j, k = triple
    return (
        f"(χ ⟨f {i}, f {j}, f {k}, f.strictMono (by decide), "
        "f.strictMono (by decide)⟩)"
    )


def values_definition(name: str, count: int, equations: list[str]) -> str:
    binders = " ".join(f"x{i}" for i in range(count))
    return f"def {name} ({binders} : Turn) : Prop :=\n  " + " ∧\n  ".join(equations)


def chain_encoding(size: int, color: str, name: str, iff_name: str) -> str:
    local = triples(range(size))
    actual = "\n        ".join(selected_triple_term(size, triple) for triple in local)
    equations = [f"x{i} = Turn.{color}" for i in range(len(local))]
    values = values_definition(name, len(local), equations)
    forward = ",\n      ".join("h (by decide) (by decide)" for _ in local)
    hypotheses = ", ".join(f"h{i}" for i in range(len(local)))
    cases = " <;> ".join(f"fin_cases {variable}" for variable in "ijk")
    predicate = "IsCap" if color == "right" else "IsCup"
    theorem = f'''theorem {iff_name} {{n : ℕ}} (χ : TripleColoring n)
    (f : Fin {size} ↪o Fin n) :
    {predicate} χ f ↔
      {name}
        {actual} := by
  constructor
  · rintro ⟨_, h⟩
    exact ⟨{forward}⟩
  · rintro ⟨{hypotheses}⟩
    refine ⟨f.strictMono, ?_⟩
    intro i j k hij hjk
    {cases} <;> simp at hij hjk <;> simp_all
'''
    return values + "\n\n" + theorem


def strong_mismatch_theorem() -> str:
    """A compact middle-color presentation of all strong-nine patterns."""
    local = triples(range(STRONG))
    colors = " ".join(f"c{i}" for i in range(STRONG))
    actual = [selected_triple_term(STRONG, triple) for triple in local]
    conclusion = " ∨\n    ".join(
        f"{term} ≠ c{triple[1]}" for term, triple in zip(actual, local)
    )
    hypotheses = ", ".join(f"h{i}" for i in range(len(local)))
    cases = " <;> ".join(f"fin_cases {variable}" for variable in "ijk")
    return f'''theorem diagonalCupBlocksK9_strongNine_mismatch
    {{n : ℕ}} (χ : TripleColoring n) (f : Fin 9 ↪o Fin n)
    (hnot : ¬ IsStrongPolygonOn χ f) {{{colors} : Turn}} :
    {conclusion} := by
  by_contra h
  push Not at h
  rcases h with ⟨{hypotheses}⟩
  apply hnot
  have hmiddle : ∀ (i j k : Fin 9), (hij : i < j) → (hjk : j < k) →
      χ ⟨f i, f j, f k, f.strictMono hij, f.strictMono hjk⟩ =
        ![c0, c1, c2, c3, c4, c5, c6, c7, c8] j := by
    intro i j k hij hjk
    {cases} <;> simp at hij hjk <;> simp_all
  intro i j k l hij hjk hkl
  exact ⟨
    (hmiddle i j k hij hjk).trans
      (hmiddle i j l hij (hjk.trans hkl)).symm,
    (hmiddle i k l (hij.trans hjk) hkl).trans
      (hmiddle j k l hjk hkl).symm⟩
'''


def mismatch_theorem(
    theorem_name: str, size: int, values_name: str, predicate: str, iff_name: str
) -> str:
    local = triples(range(size))
    count = len(local)
    binders = " ".join(f"x{i}" for i in range(count))
    actual = [selected_triple_term(size, triple) for triple in local]
    conclusion = " ∨\n    ".join(f"{term} ≠ x{i}" for i, term in enumerate(actual))
    hypotheses = ", ".join(f"h{i}" for i in range(count))
    rewrites = ", ".join(f"h{i}" for i in range(count))
    arguments = " ".join(f"x{i}" for i in range(count))
    return f'''theorem {theorem_name} {{n : ℕ}} (χ : TripleColoring n)
    (f : Fin {size} ↪o Fin n) (hnot : ¬ {predicate} χ f)
    {{{binders} : Turn}} (htarget : {values_name} {arguments}) :
    {conclusion} := by
  by_contra h
  push Not at h
  rcases h with ⟨{hypotheses}⟩
  apply hnot
  rw [{iff_name}]
  simpa [{rewrites}] using htarget
'''


def write_encoding(lean_dir: Path) -> None:
    def header() -> str:
        return f'''module

public import ErdosSzekeres.StructuralChargingPascalCupBlocks

@[expose] public section

/- This file is generated by scripts/generate_diagonal_k9_lean.py. -/

set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace ErdosSzekeres

noncomputable section

'''
    footer = "\nend\n\nend ErdosSzekeres\n\nend\n"
    cap = header()
    cap += chain_encoding(4, "right", f"{PREFIX}CapFourValues", "diagonalCupBlocksK9_isCap_finFour_iff")
    cap += "\n" + mismatch_theorem(
        "diagonalCupBlocksK9_capFour_mismatch", 4, f"{PREFIX}CapFourValues", "IsCap", "diagonalCupBlocksK9_isCap_finFour_iff"
    )
    cap += footer
    write_if_changed(lean_dir / f"{PREFIX}CapEncoding.lean", cap)
    cup = header()
    cup += chain_encoding(9, "left", f"{PREFIX}CupNineValues", "diagonalCupBlocksK9_isCup_finNine_iff")
    cup += "\n" + mismatch_theorem(
        "diagonalCupBlocksK9_cupNine_mismatch", 9, f"{PREFIX}CupNineValues", "IsCup", "diagonalCupBlocksK9_isCup_finNine_iff"
    )
    cup += footer
    write_if_changed(lean_dir / f"{PREFIX}CupEncoding.lean", cup)
    strong = header() + strong_mismatch_theorem() + footer
    write_if_changed(lean_dir / f"{PREFIX}StrongEncoding.lean", strong)
    source = f'''module

public import ErdosSzekeres.{PREFIX}CapEncoding
public import ErdosSzekeres.{PREFIX}CupEncoding
public import ErdosSzekeres.{PREFIX}StrongEncoding

@[expose] public section

/- This file is generated by scripts/generate_diagonal_k9_lean.py. -/

end
'''
    write_if_changed(lean_dir / f"{PREFIX}Encoding.lean", source)


def semantic_clause_proof(origin: Origin) -> str:
    targets = [turn_term(bit) for bit in origin.values]
    if origin.kind == "quad":
        a, b, c, d = origin.vertices
        named = " ".join(f"({name} := {target})" for name, target in zip("ABCD", targets))
        return f'''(by
      have hm := turnSequence_mismatch
        (hallowed {a} {b} {c} {d} (by decide) (by decide) (by decide))
        {named} (by simp [TurnSequenceAllowed])
      simpa only [Turn.ne_right_iff_eq_left] using hm)'''
    if origin.kind == "unit":
        i, j, k = origin.vertices
        return f'''(by
      simpa using h{origin.side} ⟨{i}, {j}, {k}, by decide, by decide⟩
        (by simp) (by simp) (by simp))'''
    size = CAP if origin.kind == "cap" else 9
    vector = ", ".join(map(str, origin.vertices))
    named = " ".join(f"(x{i} := {target})" for i, target in enumerate(targets))
    if origin.kind == "cap":
        call = "diagonalCupBlocksK9_capFour_mismatch χ f (hnoCap f)"
        values_name = f"{PREFIX}CapFourValues"
    elif origin.kind == "cup":
        call = "diagonalCupBlocksK9_cupNine_mismatch χ f (hnoCup f)"
        values_name = f"{PREFIX}CupNineValues"
    else:
        local = triples(range(STRONG))
        by_middle: dict[int, bool] = {}
        for triple, value in zip(local, origin.values):
            middle = triple[1]
            if middle in by_middle and by_middle[middle] != value:
                raise ValueError("strong pattern is not middle-determined")
            by_middle[middle] = value
        middle_targets = [by_middle.get(index, False) for index in range(STRONG)]
        middle_named = " ".join(
            f"(c{index} := {turn_term(value)})"
            for index, value in enumerate(middle_targets)
        )
        return f'''(by
      let f : Fin 9 ↪o Fin 15 := OrderEmbedding.ofStrictMono ![{vector}] (by decide)
      have hm := diagonalCupBlocksK9_strongNine_mismatch χ f (hnoStrong f)
        {middle_named}
      simpa only [f, Turn.ne_right_iff_eq_left] using hm)'''
    return f'''(by
      let f : Fin {size} ↪o Fin 15 := OrderEmbedding.ofStrictMono ![{vector}] (by decide)
      have hm := {call} {named} (by simp [{values_name}])
      simpa only [f, Turn.ne_right_iff_eq_left] using hm)'''


def bad_clause_contradiction(proof: str, clause: tuple[int, ...]) -> str:
    if len(clause) == 1:
        contradiction = "hbad hsat" if clause[0] > 0 else "hsat hbad"
        return (
            f"(by\n      intro hbad\n      have hsat := {proof}\n"
            f"      exact {contradiction})"
        )
    bad_names = ", ".join(f"hb{i}" for i in range(len(clause)))
    cases = " | ".join("hs" for _ in clause)
    contradictions = "\n".join(
        f"      · exact {'hb' + str(i) + ' hs' if literal > 0 else 'hs hb' + str(i)}"
        for i, literal in enumerate(clause)
    )
    return (
        f"(by\n      intro hbad\n      have hsat := {proof}\n"
        f"      rcases hbad with ⟨{bad_names}⟩\n"
        f"      rcases hsat with {cases}\n{contradictions})"
    )


def set_literal(start: int, stop: int) -> str:
    return "{" + ", ".join(map(str, range(start, stop))) + "}"


def assumptions(orientation: Orientation) -> str:
    return f'''(hallowed : ∀ (a b c d : Fin 15),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩))
    (hnoCap : ∀ f : Fin 4 ↪o Fin 15, ¬ IsCap χ f)
    (hnoCup : ∀ f : Fin 9 ↪o Fin 15, ¬ IsCup χ f)
    (hnoStrong : ∀ f : Fin 9 ↪o Fin 15, ¬ IsStrongPolygonOn χ f)
    (hleft : IsCupSet χ {set_literal(0, orientation.left)})
    (hright : IsCupSet χ {set_literal(orientation.left, N)})'''


def write_unsat(repo: Path, run_dir: Path, orientation: Orientation) -> None:
    source_cnf = run_dir / f"{orientation.source_stem}-dense-core.cnf"
    source_lrat = run_dir / f"{orientation.source_stem}-dense-core.lrat"
    target_stem = f"k9-cup-blocks-{orientation.left}-{orientation.right}-dense"
    target_cnf = repo / "certificates" / f"{target_stem}.cnf"
    target_lrat = repo / "certificates" / f"{target_stem}.lrat"
    if sha256(source_cnf) != orientation.expected_cnf_sha256 or sha256(source_lrat) != orientation.expected_lrat_sha256:
        raise ValueError(f"{orientation.tag}: frozen dense artifact hash mismatch")
    write_if_changed(target_cnf, source_cnf.read_bytes())
    write_if_changed(target_lrat, source_lrat.read_bytes())
    theorem = f"diagonalCupBlocksK9Dense{orientation.tag}_lrat_unsat"
    lean = f'''module

public import Mathlib.Tactic.Sat.FromLRAT

@[expose] public section

/-! Kernel-checked LRAT certificate for the normalized `{orientation.left}+{orientation.right}` k=9 core. -/

namespace ErdosSzekeres

lrat_proof {theorem}
  (include_str "../certificates/{target_stem}.cnf")
  (include_str "../certificates/{target_stem}.lrat")

end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}Dense{orientation.tag}Unsat.lean", lean)


def write_orientation_modules(
    repo: Path, run_dir: Path, orientation: Orientation
) -> dict[str, object]:
    old_variables, clauses, origins = retained_clauses(run_dir, orientation)
    lean_dir = repo / "ErdosSzekeres"
    tag_prefix = f"{PREFIX}Dense{orientation.tag}"
    bad_props: list[str] = []
    for clause in clauses:
        literals = [
            f"¬{triple_prop(old_variables[abs(literal) - 1])}"
            if literal > 0
            else triple_prop(old_variables[abs(literal) - 1])
            for literal in clause
        ]
        bad_props.append("(" + " ∧ ".join(literals) + ")")
    prop_chunks = balanced_chunks(bad_props, orientation.chunks)
    proof_items = [
        bad_clause_contradiction(semantic_clause_proof(origin), clause)
        for origin, clause in zip(origins, clauses)
    ]
    proof_chunks = balanced_chunks(proof_items, orientation.chunks)
    common_header = f'''@[expose] public section

/- This file is generated by scripts/generate_diagonal_k9_lean.py. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace ErdosSzekeres

'''
    for index, (props, proofs) in enumerate(zip(prop_chunks, proof_chunks)):
        chunk_name = f"{tag_prefix}BadChunk{index}"
        definition = f"def {chunk_name} (χ : TripleColoring 15) : Prop :=\n    " + balanced_join(props, "∨")
        theorem = f'''theorem diagonalCupBlocksK9Dense{orientation.tag}CNFChunk{index}_of_constraints
    (χ : TripleColoring 15) {assumptions(orientation)} :
    ¬ {chunk_name} χ := by
  unfold {chunk_name}
  exact {balanced_not_or_proof(proofs)}'''
        source = (
            f"module\n\npublic import ErdosSzekeres.{PREFIX}Encoding\n\n"
            + common_header
            + definition
            + "\n\n"
            + theorem
            + "\n\nend ErdosSzekeres\n\nend\n"
        )
        write_if_changed(lean_dir / f"{PREFIX}Dense{orientation.tag}CNFChunk{index:02}.lean", source)

    imports = "\n".join(
        f"public import ErdosSzekeres.{PREFIX}Dense{orientation.tag}CNFChunk{index:02}"
        for index in range(orientation.chunks)
    )
    imports += f"\npublic import ErdosSzekeres.{PREFIX}Dense{orientation.tag}Unsat"
    chunk_names = [f"{tag_prefix}BadChunk{index}" for index in range(orientation.chunks)]
    bad_name = f"{tag_prefix}Bad"
    cnf_name = f"{tag_prefix}CNF"
    bad_definition = f"def {bad_name} (χ : TripleColoring 15) : Prop :=\n    " + balanced_join(
        [f"{name} χ" for name in chunk_names], "∨"
    )
    arguments = " ".join(f"({triple_prop(old_variable)})" for old_variable in old_variables)
    steps = "\n  ".join(
        [
            f"have h{index} := diagonalCupBlocksK9Dense{orientation.tag}CNFChunk{index}_of_constraints χ hallowed hnoCap hnoCup hnoStrong hleft hright"
            for index in range(orientation.chunks)
        ]
        + [f"unfold {cnf_name} {bad_name}", "tauto"]
    )
    root = f'''module

{imports}

{common_header}{bad_definition}

def {cnf_name} (χ : TripleColoring 15) : Prop := ¬ {bad_name} χ

theorem diagonalCupBlocksK9Dense{orientation.tag}CNF_unsat
    (χ : TripleColoring 15) : ¬ {cnf_name} χ := by
  intro hcnf
  have hcertificate := diagonalCupBlocksK9Dense{orientation.tag}_lrat_unsat {arguments}
  apply hcnf
  unfold {bad_name} {' '.join(chunk_names)}
  exact hcertificate

theorem diagonalCupBlocksK9Dense{orientation.tag}CNF_of_constraints
    (χ : TripleColoring 15) {assumptions(orientation)} : {cnf_name} χ := by
  {steps}

end ErdosSzekeres

end
'''
    write_if_changed(lean_dir / f"{PREFIX}Dense{orientation.tag}CNFGenerated.lean", root)
    return {
        "orientation": f"{orientation.left}+{orientation.right}",
        "variables": len(old_variables),
        "clauses": len(clauses),
        "family_counts": orientation.expected_families,
        "cnf_sha256": orientation.expected_cnf_sha256,
        "lrat_sha256": orientation.expected_lrat_sha256,
    }


def contains_helper(name: str, size: int, predicate: str, set_predicate: str) -> str:
    return f'''theorem {name} {{n : ℕ}} {{χ : TripleColoring n}}
    {{f : Fin {size} ↪o Fin n}} (h : {predicate} χ f) :
    {set_predicate} χ Finset.univ {size} := by
  refine ⟨Finset.univ.image f, by simp, ?_, ?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ f.injective
  · exact FinsetPolygon.{predicate}.image h

'''


def write_normalized(repo: Path) -> None:
    lean_dir = repo / "ErdosSzekeres"
    source = f'''module

public import ErdosSzekeres.{PREFIX}Dense78CNFGenerated
public import ErdosSzekeres.{PREFIX}Dense87CNFGenerated

@[expose] public section

/-! Normalized semantic consequences of the two dense k=9 LRAT cores. -/

set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace ErdosSzekeres

'''
    source += contains_helper(
        "diagonalCupBlocksK9_containsCapSet_univ_of_finFour", 4, "IsCap", "ContainsCapSet"
    )
    source += contains_helper(
        "diagonalCupBlocksK9_containsCupSet_univ_of_finNine", 9, "IsCup", "ContainsCupSet"
    )
    source += contains_helper(
        "diagonalCupBlocksK9_containsStrongPolygonSet_univ_of_finNine",
        9,
        "IsStrongPolygonOn",
        "ContainsStrongPolygonSet",
    ).replace("FinsetPolygon.IsStrongPolygonOn.image", "FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image")

    for orientation in ORIENTATIONS:
        left_set = set_literal(0, orientation.left)
        right_set = set_literal(orientation.left, N)
        source += f'''def {PREFIX}FinFifteen{orientation.tag} : Prop :=
  ∀ χ : TripleColoring 15,
    IsCupSet χ {left_set} →
      IsCupSet χ {right_set} →
        OneChangeOn χ Finset.univ →
          ContainsCapSet χ Finset.univ 4 ∨
            ContainsCupSet χ Finset.univ 9 ∨
              ContainsStrongPolygonSet χ Finset.univ 9

theorem diagonalCupBlocksK9FinFifteen{orientation.tag} :
    {PREFIX}FinFifteen{orientation.tag} := by
  intro χ hleft hright hone
  by_contra hout
  have hnoCapSet : ¬ ContainsCapSet χ Finset.univ 4 :=
    fun hcap ↦ hout (Or.inl hcap)
  have hnoCupSet : ¬ ContainsCupSet χ Finset.univ 9 :=
    fun hcup ↦ hout (Or.inr (Or.inl hcup))
  have hnoStrongSet : ¬ ContainsStrongPolygonSet χ Finset.univ 9 :=
    fun hstrong ↦ hout (Or.inr (Or.inr hstrong))
  have hnoCap : ∀ f : Fin 4 ↪o Fin 15, ¬ IsCap χ f := by
    intro f hcap
    exact hnoCapSet (diagonalCupBlocksK9_containsCapSet_univ_of_finFour hcap)
  have hnoCup : ∀ f : Fin 9 ↪o Fin 15, ¬ IsCup χ f := by
    intro f hcup
    exact hnoCupSet (diagonalCupBlocksK9_containsCupSet_univ_of_finNine hcup)
  have hnoStrong : ∀ f : Fin 9 ↪o Fin 15, ¬ IsStrongPolygonOn χ f := by
    intro f hstrong
    exact hnoStrongSet
      (diagonalCupBlocksK9_containsStrongPolygonSet_univ_of_finNine hstrong)
  have hallowed : ∀ (a b c d : Fin 15),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    exact hone hab hbc hcd (by simp) (by simp) (by simp) (by simp)
  exact diagonalCupBlocksK9Dense{orientation.tag}CNF_unsat χ
    (diagonalCupBlocksK9Dense{orientation.tag}CNF_of_constraints χ
      hallowed hnoCap hnoCup hnoStrong hleft hright)

'''
    source += "end ErdosSzekeres\n\nend\n"
    write_if_changed(lean_dir / f"{PREFIX}Normalized.lean", source)


def vector_entries(left_size: int, right_size: int) -> str:
    left = [f"le {index}" for index in range(left_size)]
    right = [f"re {index}" for index in range(right_size)]
    rows: list[str] = []
    entries = left + right
    for start in range(0, len(entries), 8):
        rows.append(", ".join(entries[start : start + 8]))
    return ",\n      ".join(rows)


def rcases_members(count: int) -> str:
    return " | ".join("rfl" for _ in range(count))


def transport_theorem(orientation: Orientation) -> str:
    left_set = set_literal(0, orientation.left)
    right_set = set_literal(orientation.left, N)
    return f'''set_option maxHeartbeats 2000000 in
theorem diagonalCupBlocksK9_{orientation.tag}_of_finFifteen
    {{n : ℕ}} {{χ : TripleColoring n}} {{left right : Finset (Fin n)}}
    (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = {orientation.left})
    (hrightCard : right.card = {orientation.right})
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 9 ∨
        ContainsStrongPolygonSet χ (left ∪ right) 9 := by
  let le : Fin {orientation.left} ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin {orientation.right} ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 15 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![{vector_entries(orientation.left, orientation.right)}] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 15 := χ.restrict f
  have hfmem : ∀ i : Fin 15, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 15, i ∈ ({left_set} : Finset (Fin 15)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with {rcases_members(orientation.left)} <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 15, i ∈ ({right_set} : Finset (Fin 15)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with {rcases_members(orientation.right)} <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {left_set} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {right_set} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := diagonalCupBlocksK9FinFifteen{orientation.tag} ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 15 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard, himageCard]
  rcases hout with hcap | hcup | hstrong
  · exact Or.inl (by simpa [himage] using containsCapSet_map_restrict f hcap)
  · exact Or.inr (Or.inl (by simpa [himage] using containsCupSet_map_restrict f hcup))
  · exact Or.inr (Or.inr (by
      simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong))

'''


def write_transport(repo: Path) -> None:
    source = f'''module

public import ErdosSzekeres.{PREFIX}Normalized

@[expose] public section

/-! Transport the normalized fifteen-vertex k=9 certificates to arbitrary blocks. -/

namespace ErdosSzekeres

'''
    for orientation in ORIENTATIONS:
        source += transport_theorem(orientation)
    source += '''/-- The exact k=9 diagonal cup-block contract. -/
theorem diagonalCupBlocksForce4kk_nine : DiagonalCupBlocksForce4kk 9 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  norm_num at hcards
  rcases hcards with ⟨hleftCard, hrightCard⟩ | ⟨hleftCard, hrightCard⟩
  · exact diagonalCupBlocksK9_78_of_finFifteen hdisjoint horder
      hleftCard hrightCard hleft hright hone
  · exact diagonalCupBlocksK9_87_of_finFifteen hdisjoint horder
      hleftCard hrightCard hleft hright hone

end ErdosSzekeres

end
'''
    write_if_changed(repo / "ErdosSzekeres" / f"{PREFIX}Certificate.lean", source)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument(
        "--source-run",
        type=Path,
        default=Path("runs/agents/20260810-three-route-forward/state567"),
    )
    parser.add_argument(
        "--audit-output",
        type=Path,
        default=Path("runs/agents/20260810-parallel-portfolio/k9/generation-audit.json"),
    )
    args = parser.parse_args()
    repo = args.repo.resolve()
    run_dir = args.source_run if args.source_run.is_absolute() else repo / args.source_run
    write_encoding(repo / "ErdosSzekeres")
    audit: list[dict[str, object]] = []
    for orientation in ORIENTATIONS:
        write_unsat(repo, run_dir, orientation)
        audit.append(write_orientation_modules(repo, run_dir, orientation))
    write_normalized(repo)
    write_transport(repo)
    audit_path = args.audit_output if args.audit_output.is_absolute() else repo / args.audit_output
    write_if_changed(
        audit_path,
        json.dumps({"schema_version": 1, "orientations": audit}, indent=2, sort_keys=True) + "\n",
    )
    print(json.dumps({"status": "generated", "audit": str(audit_path), "orientations": audit}, sort_keys=True))


if __name__ == "__main__":
    main()
