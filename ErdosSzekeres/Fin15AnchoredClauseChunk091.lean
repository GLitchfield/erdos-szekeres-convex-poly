module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 091. -/

theorem fin15Anchored_clause11648 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11649 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 Fin15AnchoredAtom1351 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11655 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1353 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11656 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1353 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11657 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1353 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11658 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1353 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1353 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1353 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1353 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1353 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 Fin15AnchoredAtom1353 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11664 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 Fin15AnchoredAtom1354 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11665 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 Fin15AnchoredAtom1354 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11666 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 Fin15AnchoredAtom1354 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11667 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 Fin15AnchoredAtom1354 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 Fin15AnchoredAtom1354 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 Fin15AnchoredAtom1354 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 Fin15AnchoredAtom1354 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 Fin15AnchoredAtom1354 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11672 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0245 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1355 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11673 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0245 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1355 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11674 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0245 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1355 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11675 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0245 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1355 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0245 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1355 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0245 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1355 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0245 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1355 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0245 Fin15AnchoredAtom0275
    Fin15AnchoredAtom0320 Fin15AnchoredAtom1355 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11680 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0241 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1356 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11681 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0241 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1356 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0241 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1356 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11683 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0241 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1356 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0241 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1356 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0241 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1356 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0241 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1356 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0241 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1356 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0241 Fin15AnchoredAtom0276
    Fin15AnchoredAtom0321 Fin15AnchoredAtom1356 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11689 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0242 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1357 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11690 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0242 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1357 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11691 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0242 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1357 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11692 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0242 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1357 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0242 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1357 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0242 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1357 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0242 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1357 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0242 Fin15AnchoredAtom0277
    Fin15AnchoredAtom0322 Fin15AnchoredAtom1357 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11697 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0243 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1358 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11698 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0243 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1358 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0243 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1358 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11700 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0243 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1358 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0243 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1358 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0243 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1358 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0243 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1358 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0243 Fin15AnchoredAtom0278
    Fin15AnchoredAtom0323 Fin15AnchoredAtom1358 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11705 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0244 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1359 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11706 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0244 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1359 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0244 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1359 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11708 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0244 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1359 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0244 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1359 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0244 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1359 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0244 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1359 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0244 Fin15AnchoredAtom0279
    Fin15AnchoredAtom0324 Fin15AnchoredAtom1359 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11713 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0245 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1360 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11714 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0245 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1360 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11715 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0245 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1360 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11716 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0245 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1360 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0245 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1360 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0245 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1360 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0245 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1360 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0245 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1360 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0240 Fin15AnchoredAtom0245 Fin15AnchoredAtom0280
    Fin15AnchoredAtom0325 Fin15AnchoredAtom1360 at hbad
  cases hcolor0 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11722 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1361 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0242 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0326 Fin15AnchoredAtom1361 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1361 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0242 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0326 Fin15AnchoredAtom1361 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom1361 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0242 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0326 Fin15AnchoredAtom1361 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom1361 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0242 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0326 Fin15AnchoredAtom1361 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11726 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11727 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11728 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11729 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11730 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0243 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0327 Fin15AnchoredAtom1362 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11737 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11738 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11739 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11740 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0244 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0328 Fin15AnchoredAtom1363 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11746 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11747 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11750 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0241 Fin15AnchoredAtom0245 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0329 Fin15AnchoredAtom1364 at hbad
  cases hcolor0 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11756 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0242 Fin15AnchoredAtom0243 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0330 Fin15AnchoredAtom1365 at hbad
  cases hcolor0 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11757 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0242 Fin15AnchoredAtom0243 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0330 Fin15AnchoredAtom1365 at hbad
  cases hcolor0 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0242 Fin15AnchoredAtom0243 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0330 Fin15AnchoredAtom1365 at hbad
  cases hcolor0 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0242 Fin15AnchoredAtom0243 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0330 Fin15AnchoredAtom1365 at hbad
  cases hcolor0 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0242 Fin15AnchoredAtom0243 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0330 Fin15AnchoredAtom1365 at hbad
  cases hcolor0 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11761 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom1366 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0242 Fin15AnchoredAtom0244 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0331 Fin15AnchoredAtom1366 at hbad
  cases hcolor0 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom1366 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0242 Fin15AnchoredAtom0244 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0331 Fin15AnchoredAtom1366 at hbad
  cases hcolor0 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom1367 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0242 Fin15AnchoredAtom0245 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0332 Fin15AnchoredAtom1367 at hbad
  cases hcolor0 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11764 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0244 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1368 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11765 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0244 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1368 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11766 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0244 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1368 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11767 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0244 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1368 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0244 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1368 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0244 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1368 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0244 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1368 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0244 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1368 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0244 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0333 Fin15AnchoredAtom1368 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11773 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0245 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1369 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11774 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0245 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1369 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause11775 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0243 Fin15AnchoredAtom0245 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0334 Fin15AnchoredAtom1369 at hbad
  cases hcolor0 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
