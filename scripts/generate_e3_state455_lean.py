#!/usr/bin/env python3
"""Generate the semantic Lean bridge for the eight-point (4,5,5) CNF."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_e3_state466_lean import (
    bad_clause_contradiction,
    balanced_chunks,
    balanced_join,
    balanced_not_or_proof,
    chain_encoding,
    mismatch_theorem,
    selected_triple_term,
    turn_term,
)
from generate_signotope_state_sat import generate, triples


N = 8
CAP = 4
CUP = 5
STRONG = 5
PREFIX = "E3State455"
CHUNK_COUNT = 8

CAP_VALUES = f"{PREFIX}CapFourValues"
CUP_VALUES = f"{PREFIX}CupFiveValues"
STRONG_VALUES = f"{PREFIX}StrongFiveValues"
CAP_IFF = f"e3State455_isCap_finFour_iff"
CUP_IFF = f"e3State455_isCup_finFive_iff"
STRONG_IFF = f"e3State455_isStrongPolygonOn_finFive_iff"


def values_definition(name: str, count: int, equations: list[str]) -> str:
    binders = " ".join(f"x{i}" for i in range(count))
    return f"def {name} ({binders} : Turn) : Prop :=\n  " + " ∧\n  ".join(equations)


def strong_encoding(size: int, values_name: str, iff_name: str) -> str:
    local_triples = triples(range(size))
    position = {triple: index for index, triple in enumerate(local_triples)}
    quads = tuple(itertools.combinations(range(size), 4))
    equations: list[str] = []
    for i, j, k, l in quads:
        equations.append(f"x{position[i, j, k]} = x{position[i, j, l]}")
        equations.append(f"x{position[i, k, l]} = x{position[j, k, l]}")
    values = values_definition(values_name, len(local_triples), equations)
    actual = "\n        ".join(selected_triple_term(size, triple) for triple in local_triples)
    forward_items: list[str] = []
    for i, j, k, l in quads:
        call = (
            f"h (i := {i}) (j := {j}) (k := {k}) (l := {l}) "
            "(by decide) (by decide) (by decide)"
        )
        forward_items.extend(
            [
                "(by simpa [TripleColoring.restrict, OrderedTriple.map] using "
                f"({call}).1)",
                "(by simpa [TripleColoring.restrict, OrderedTriple.map] using "
                f"({call}).2)",
            ]
        )
    forward = ",\n      ".join(forward_items)
    hypotheses = ", ".join(f"h{i}" for i in range(len(equations)))
    cases = " <;> ".join(f"fin_cases {variable}" for variable in "ijkl")
    theorem = f'''theorem {iff_name} {{n : ℕ}} (χ : TripleColoring n)
    (f : Fin {size} ↪o Fin n) :
    IsStrongPolygonOn χ f ↔
      {values_name}
        {actual} := by
  constructor
  · intro h
    exact ⟨{forward}⟩
  · rintro ⟨{hypotheses}⟩
    intro i j k l hij hjk hkl
    {cases} <;>
      simp [TripleColoring.restrict, OrderedTriple.map] at hij hjk hkl ⊢ <;> simp_all
'''
    return values + "\n\n" + theorem


def write_encoding(directory: Path) -> None:
    source = '''module

public import ErdosSzekeres.ES5Encoding
public import ErdosSzekeres.E3State455Unsat

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace ErdosSzekeres

noncomputable section

'''
    source += chain_encoding(CAP, "right", CAP_VALUES, CAP_IFF)
    source += "\n" + chain_encoding(CUP, "left", CUP_VALUES, CUP_IFF)
    source += "\n" + strong_encoding(STRONG, STRONG_VALUES, STRONG_IFF)
    source += "\n" + mismatch_theorem(
        "e3State455_capFour_mismatch", CAP, CAP_VALUES, "IsCap", CAP_IFF
    )
    source += "\n" + mismatch_theorem(
        "e3State455_cupFive_mismatch", CUP, CUP_VALUES, "IsCup", CUP_IFF
    )
    source += "\n" + mismatch_theorem(
        "e3State455_strongFive_mismatch",
        STRONG,
        STRONG_VALUES,
        "IsStrongPolygonOn",
        STRONG_IFF,
    )
    source += "\nend\n\nend ErdosSzekeres\n\nend\n"
    (directory / f"{PREFIX}Encoding.lean").write_text(source, encoding="utf-8")


def semantic_clause_proof(
    kind: str, vertices: tuple[int, ...], bits: tuple[bool, ...]
) -> str:
    targets = [turn_term(bit) for bit in bits]
    if kind == "quad":
        a, b, c, d = vertices
        named = " ".join(
            f"({name} := {target})" for name, target in zip("ABCD", targets)
        )
        return f'''(by
      have hm := turnSequence_mismatch
        (hallowed {a} {b} {c} {d} (by decide) (by decide) (by decide))
        {named} (by simp [TurnSequenceAllowed])
      simpa only [Turn.ne_right_iff_eq_left] using hm)'''

    size = CAP if kind == "cap" else CUP if kind == "cup" else STRONG
    vector = ", ".join(map(str, vertices))
    named = " ".join(f"(x{i} := {target})" for i, target in enumerate(targets))
    if kind == "cap":
        call = "e3State455_capFour_mismatch χ f (hnoCap f)"
        target = CAP_VALUES
    elif kind == "cup":
        call = "e3State455_cupFive_mismatch χ f (hnoCup f)"
        target = CUP_VALUES
    else:
        call = "e3State455_strongFive_mismatch χ f (hnoStrong f)"
        target = STRONG_VALUES
    return f'''(by
      let f : Fin {size} ↪o Fin {N} := OrderEmbedding.ofStrictMono ![{vector}] (by decide)
      have hm := {call} {named} (by simp [{target}])
      simpa only [f, Turn.ne_right_iff_eq_left] using hm)'''


def write_modules(directory: Path) -> tuple[int, int]:
    all_triples, clauses, origins, _, _ = generate(N, CAP, CUP, STRONG)

    def triple_term(index: int) -> str:
        a, b, c = all_triples[index]
        return f"(χ ⟨{a}, {b}, {c}, by decide, by decide⟩ = Turn.left)"

    bad_clause_props: list[str] = []
    for clause in clauses:
        bad_literals = [
            f"¬{triple_term(abs(literal) - 1)}"
            if literal > 0
            else triple_term(abs(literal) - 1)
            for literal in clause
        ]
        bad_clause_props.append("(" + " ∧ ".join(bad_literals) + ")")
    prop_chunks = balanced_chunks(bad_clause_props, CHUNK_COUNT)
    chunk_definitions = [
        f"def {PREFIX}BadChunk{i} (χ : TripleColoring {N}) : Prop :=\n    "
        + balanced_join(chunk, "∨")
        for i, chunk in enumerate(prop_chunks)
    ]
    bad_disjunction = balanced_join(
        [f"{PREFIX}BadChunk{i} χ" for i in range(len(prop_chunks))], "∨"
    )

    header = '''@[expose] public section

/- This file is generated by scripts/generate_e3_state455_lean.py. -/

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

namespace ErdosSzekeres

'''
    proofs = [
        bad_clause_contradiction(semantic_clause_proof(*origin), clause)
        for origin, clause in zip(origins, clauses)
    ]
    proof_chunks = balanced_chunks(proofs, CHUNK_COUNT)
    assumptions = f'''(hallowed : ∀ (a b c d : Fin {N}),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩))
    (hnoCap : ∀ f : Fin {CAP} ↪o Fin {N}, ¬ IsCap χ f)
    (hnoCup : ∀ f : Fin {CUP} ↪o Fin {N}, ¬ IsCup χ f)
    (hnoStrong : ∀ f : Fin {STRONG} ↪o Fin {N}, ¬ IsStrongPolygonOn χ f)'''
    for index, (definition, chunk) in enumerate(zip(chunk_definitions, proof_chunks)):
        theorem = (
            f"theorem e3State455CNFChunk{index}_of_constraints "
            f"(χ : TripleColoring {N})\n"
            f"    {assumptions} : ¬ {PREFIX}BadChunk{index} χ := by\n"
            f"  unfold {PREFIX}BadChunk{index}\n"
            f"  exact {balanced_not_or_proof(chunk)}"
        )
        source = (
            f"module\n\npublic import ErdosSzekeres.{PREFIX}Encoding\n\n"
            + header
            + definition
            + "\n\n"
            + theorem
            + "\n\nend ErdosSzekeres\n\nend\n"
        )
        (directory / f"{PREFIX}CNFChunk{index:02}.lean").write_text(
            source, encoding="utf-8"
        )

    imports = "\n".join(
        f"public import ErdosSzekeres.{PREFIX}CNFChunk{index:02}"
        for index in range(len(proof_chunks))
    )
    arguments = " ".join(f"({triple_term(index)})" for index in range(len(all_triples)))
    chunk_names = " ".join(f"{PREFIX}BadChunk{index}" for index in range(len(prop_chunks)))
    steps = "\n  ".join(
        [
            f"have h{index} := e3State455CNFChunk{index}_of_constraints χ "
            "hallowed hnoCap hnoCup hnoStrong"
            for index in range(len(proof_chunks))
        ]
        + [f"unfold {PREFIX}CNF {PREFIX}Bad", "tauto"]
    )
    main = f'''module

{imports}

{header}def {PREFIX}Bad (χ : TripleColoring {N}) : Prop :=
    {bad_disjunction}

def {PREFIX}CNF (χ : TripleColoring {N}) : Prop := ¬ {PREFIX}Bad χ

theorem e3State455CNF_unsat (χ : TripleColoring {N}) : ¬ {PREFIX}CNF χ := by
  intro hcnf
  have hcertificate := e3State455_cnf_unsat {arguments}
  apply hcnf
  unfold {PREFIX}Bad {chunk_names}
  exact hcertificate

theorem e3State455CNF_of_constraints (χ : TripleColoring {N})
    {assumptions} : {PREFIX}CNF χ := by
  {steps}

end ErdosSzekeres

end
'''
    (directory / f"{PREFIX}CNFGenerated.lean").write_text(main, encoding="utf-8")
    return len(clauses), len(proof_chunks)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    write_encoding(args.directory)
    clauses, chunks = write_modules(args.directory)
    print(f"clauses={clauses} chunks={chunks} directory={args.directory}")


if __name__ == "__main__":
    main()
