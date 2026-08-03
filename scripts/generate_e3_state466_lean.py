#!/usr/bin/env python3
"""Generate the semantic Lean bridge for the twelve-point (4,6,6) CNF.

The separately checked LRAT theorem only knows the DIMACS clauses.  These
generated modules prove that a rank-three signotope with no four-cap, no
six-cup, and no strong six-set satisfies every one of those clauses.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_signotope_state_sat import generate, triples


N = 12
CAP = 4
CUP = 6
STRONG = 6
PREFIX = "E3State466"
CHUNK_COUNT = 128
DEPENDENCY_CHAINS = 8


def balanced_join(items: list[str], operator: str) -> str:
    if len(items) == 1:
        return items[0]
    midpoint = len(items) // 2
    return (
        f"({balanced_join(items[:midpoint], operator)} {operator} "
        f"{balanced_join(items[midpoint:], operator)})"
    )


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
    """Cut a balanced expression tree into `count` definitionally aligned subtrees."""
    if count == 1:
        return [items]
    if count <= 0 or count > len(items) or count % 2 != 0:
        raise ValueError("balanced chunk count must be an even positive divisor tree")
    midpoint = len(items) // 2
    half = count // 2
    return (
        balanced_chunks(items[:midpoint], half)
        + balanced_chunks(items[midpoint:], half)
    )


def turn_term(bit: bool) -> str:
    return "Turn.left" if bit else "Turn.right"


def tuple_arguments(prefix: str, count: int) -> str:
    return " ".join(f"{prefix}{i}" for i in range(count))


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
    actual = "\n        ".join(selected_triple_term(size, t) for t in local)
    equations = [f"x{i} = Turn.{color}" for i in range(len(local))]
    values = values_definition(name, len(local), equations)
    forward = ",\n      ".join(
        "h (by decide) (by decide)" for _ in local
    )
    indices = " <;> ".join(f"fin_cases {v}" for v in "ijk")
    predicate = "IsCap" if color == "right" else "IsCup"
    theorem = f'''theorem {iff_name} {{n : ℕ}} (χ : TripleColoring n)
    (f : Fin {size} ↪o Fin n) :
    {predicate} χ f ↔
      {name}
        {actual} := by
  constructor
  · rintro ⟨_, h⟩
    exact ⟨{forward}⟩
  · rintro ⟨{tuple_arguments("h", len(local)).replace(" ", ", ")}⟩
    refine ⟨f.strictMono, ?_⟩
    intro i j k hij hjk
    {indices} <;> simp at hij hjk <;> simp_all
'''
    return values + "\n\n" + theorem


def strong_encoding() -> str:
    local_triples = triples(range(STRONG))
    position = {triple: i for i, triple in enumerate(local_triples)}
    quads = tuple(itertools.combinations(range(STRONG), 4))
    equations = []
    for i, j, k, l in quads:
        equations.append(f"x{position[i, j, k]} = x{position[i, j, l]}")
        equations.append(f"x{position[i, k, l]} = x{position[j, k, l]}")
    values = values_definition("StrongSixValues", len(local_triples), equations)
    actual = "\n        ".join(selected_triple_term(STRONG, t) for t in local_triples)
    forward_items = []
    for i, j, k, l in quads:
        call = f"h (i := {i}) (j := {j}) (k := {k}) (l := {l}) (by decide) (by decide) (by decide)"
        forward_items.extend([
            f"(by simpa [TripleColoring.restrict, OrderedTriple.map] using ({call}).1)",
            f"(by simpa [TripleColoring.restrict, OrderedTriple.map] using ({call}).2)",
        ])
    forward = ",\n      ".join(forward_items)
    hypotheses = ", ".join(f"h{i}" for i in range(len(equations)))
    cases = " <;> ".join(f"fin_cases {v}" for v in "ijkl")
    theorem = f'''theorem isStrongPolygonOn_finSix_iff {{n : ℕ}} (χ : TripleColoring n)
    (f : Fin 6 ↪o Fin n) :
    IsStrongPolygonOn χ f ↔
      StrongSixValues
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


def mismatch_theorem(
    theorem_name: str,
    size: int,
    values_name: str,
    predicate: str,
    iff_name: str,
) -> str:
    local = triples(range(size))
    count = len(local)
    xbinders = " ".join(f"x{i}" for i in range(count))
    actual = [selected_triple_term(size, t) for t in local]
    conclusion = " ∨\n    ".join(f"{term} ≠ x{i}" for i, term in enumerate(actual))
    hs = ", ".join(f"h{i}" for i in range(count))
    rewrites = ", ".join(f"h{i}" for i in range(count))
    return f'''theorem {theorem_name} {{n : ℕ}} (χ : TripleColoring n)
    (f : Fin {size} ↪o Fin n) (hnot : ¬ {predicate} χ f)
    {{{xbinders} : Turn}}
    (htarget : {values_name} {tuple_arguments("x", count)}) :
    {conclusion} := by
  by_contra h
  push Not at h
  rcases h with ⟨{hs}⟩
  apply hnot
  rw [{iff_name}]
  simpa [{rewrites}] using htarget
'''


def write_encoding(directory: Path) -> None:
    source = '''module

public import ErdosSzekeres.ES5Encoding
public import ErdosSzekeres.E3State466Unsat

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace ErdosSzekeres

noncomputable section

'''
    source += chain_encoding(4, "right", "CapFourValues", "isCap_finFour_iff")
    source += "\n" + chain_encoding(6, "left", "CupSixValues", "isCup_finSix_iff")
    source += "\n" + strong_encoding()
    source += "\n" + mismatch_theorem(
        "capFour_mismatch", 4, "CapFourValues", "IsCap", "isCap_finFour_iff"
    )
    source += "\n" + mismatch_theorem(
        "cupSix_mismatch", 6, "CupSixValues", "IsCup", "isCup_finSix_iff"
    )
    source += "\n" + mismatch_theorem(
        "strongSix_mismatch", 6, "StrongSixValues", "IsStrongPolygonOn",
        "isStrongPolygonOn_finSix_iff"
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

    size = CAP if kind == "cap" else 6
    vector = ", ".join(map(str, vertices))
    named = " ".join(f"(x{i} := {target})" for i, target in enumerate(targets))
    if kind == "cap":
        call = "capFour_mismatch χ f (hnoCap f)"
        target = "CapFourValues"
    elif kind == "cup":
        call = "cupSix_mismatch χ f (hnoCup f)"
        target = "CupSixValues"
    else:
        call = "strongSix_mismatch χ f (hnoStrong f)"
        target = "StrongSixValues"
    return f'''(by
      let f : Fin {size} ↪o Fin 12 := OrderEmbedding.ofStrictMono ![{vector}] (by decide)
      have hm := {call} {named} (by simp [{target}])
      simpa only [f, Turn.ne_right_iff_eq_left] using hm)'''


def bad_clause_contradiction(proof: str, clause: list[int]) -> str:
    bad_names = ", ".join(f"hb{i}" for i in range(len(clause)))
    cases = " | ".join("hs" for _ in clause)
    contradictions = "\n".join(
        f"      · exact {'hb' + str(i) + ' hs' if lit > 0 else 'hs hb' + str(i)}"
        for i, lit in enumerate(clause)
    )
    return (
        f"(by\n      intro hbad\n      have hsat := {proof}\n"
        f"      rcases hbad with ⟨{bad_names}⟩\n"
        f"      rcases hsat with {cases}\n{contradictions})"
    )


def write_modules(directory: Path) -> tuple[int, int]:
    all_triples, clauses, origins, _, _ = generate(N, CAP, CUP, STRONG)

    def triple_term(index: int) -> str:
        a, b, c = all_triples[index]
        return f"(χ ⟨{a}, {b}, {c}, by decide, by decide⟩ = Turn.left)"

    bad_clause_props = []
    for clause in clauses:
        bad_literals = [
            f"¬{triple_term(abs(lit) - 1)}" if lit > 0
            else triple_term(abs(lit) - 1)
            for lit in clause
        ]
        bad_clause_props.append("(" + " ∧ ".join(bad_literals) + ")")
    prop_chunks = balanced_chunks(bad_clause_props, CHUNK_COUNT)
    chunk_definitions = [
        f"def {PREFIX}BadChunk{i} (χ : TripleColoring 12) : Prop :=\n    "
        + balanced_join(chunk, "∨")
        for i, chunk in enumerate(prop_chunks)
    ]
    bad_disjunction = balanced_join(
        [f"{PREFIX}BadChunk{i} χ" for i in range(len(prop_chunks))], "∨"
    )

    header = '''@[expose] public section

/- This file is generated by scripts/generate_e3_state466_lean.py. -/

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
    assumptions = '''(hallowed : ∀ (a b c d : Fin 12),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩))
    (hnoCap : ∀ f : Fin 4 ↪o Fin 12, ¬ IsCap χ f)
    (hnoCup : ∀ f : Fin 6 ↪o Fin 12, ¬ IsCup χ f)
    (hnoStrong : ∀ f : Fin 6 ↪o Fin 12, ¬ IsStrongPolygonOn χ f)'''
    for i, (definition, chunk) in enumerate(zip(chunk_definitions, proof_chunks)):
        theorem = (
            f"theorem e3State466CNFChunk{i}_of_constraints (χ : TripleColoring 12)\n"
            f"    {assumptions} : ¬ {PREFIX}BadChunk{i} χ := by\n"
            f"  unfold {PREFIX}BadChunk{i}\n"
            f"  exact {balanced_not_or_proof(chunk)}"
        )
        imports = f"module\n\npublic import ErdosSzekeres.{PREFIX}Encoding"
        if i >= DEPENDENCY_CHAINS:
            imports += (
                f"\nimport ErdosSzekeres.{PREFIX}CNFChunk"
                f"{i - DEPENDENCY_CHAINS:03}"
            )
        source = (
            imports + "\n\n" + header + definition + "\n\n"
            + theorem + "\n\nend ErdosSzekeres\n\nend\n"
        )
        (directory / f"{PREFIX}CNFChunk{i:03}.lean").write_text(source, encoding="utf-8")

    imports = "\n".join(
        f"public import ErdosSzekeres.{PREFIX}CNFChunk{i:03}"
        for i in range(len(proof_chunks))
    )
    arguments = " ".join(f"({triple_term(i)})" for i in range(len(all_triples)))
    chunk_names = " ".join(f"{PREFIX}BadChunk{i}" for i in range(len(prop_chunks)))
    steps = "\n  ".join(
        [
            f"have h{i} := e3State466CNFChunk{i}_of_constraints χ "
            "hallowed hnoCap hnoCup hnoStrong"
            for i in range(len(proof_chunks))
        ]
        + [f"unfold {PREFIX}CNF {PREFIX}Bad", "tauto"]
    )
    main = f'''module

{imports}

{header}def {PREFIX}Bad (χ : TripleColoring 12) : Prop :=
    {bad_disjunction}

def {PREFIX}CNF (χ : TripleColoring 12) : Prop := ¬ {PREFIX}Bad χ

theorem e3State466CNF_unsat (χ : TripleColoring 12) : ¬ {PREFIX}CNF χ := by
  intro hcnf
  have hcertificate := e3State466_cnf_unsat {arguments}
  apply hcnf
  unfold {PREFIX}Bad {chunk_names}
  exact hcertificate

theorem e3State466CNF_of_constraints (χ : TripleColoring 12)
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
