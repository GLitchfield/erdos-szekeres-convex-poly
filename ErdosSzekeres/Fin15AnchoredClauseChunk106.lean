module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 106. -/

theorem fin15Anchored_clause13568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0316 Fin15AnchoredAtom0320 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1584 at hbad
  cases hcolor0 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13574 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13575 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13576 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13577 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13579 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0319 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1588 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13585 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13586 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13587 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13588 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0318 Fin15AnchoredAtom0320 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1589 at hbad
  cases hcolor0 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13594 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13595 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13597 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13598 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13599 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0319 Fin15AnchoredAtom0320 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1590 at hbad
  cases hcolor0 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13605 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13608 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13609 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0322 Fin15AnchoredAtom0326
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1591 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13616 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13617 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13618 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13619 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13620 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13621 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13622 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0323 Fin15AnchoredAtom0327
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1592 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13628 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1593 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13629 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1593 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1593 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13631 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1593 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1593 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1593 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1593 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0324 Fin15AnchoredAtom0328
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1593 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13636 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1594 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13637 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1594 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13638 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1594 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1594 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1594 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1594 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1594 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0321 Fin15AnchoredAtom0325 Fin15AnchoredAtom0329
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1594 at hbad
  cases hcolor0 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13644 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1595 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13645 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1595 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1595 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1595 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1595 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0323 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1595 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13650 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1596 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13651 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1596 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13652 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1596 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13653 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1596 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1596 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0324 Fin15AnchoredAtom0331
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1596 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13656 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1597 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13657 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1597 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13658 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1597 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13659 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1597 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1597 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0322 Fin15AnchoredAtom0325 Fin15AnchoredAtom0332
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1597 at hbad
  cases hcolor0 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13662 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13663 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13664 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13665 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13666 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0324 Fin15AnchoredAtom0333
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1598 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13672 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1599 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13673 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1599 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13674 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1599 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13675 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1599 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1599 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1599 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1599 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1599 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0323 Fin15AnchoredAtom0325 Fin15AnchoredAtom0334
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1599 at hbad
  cases hcolor0 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13681 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1600 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1600 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13683 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1600 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13684 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1600 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1600 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1600 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1600 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0324 Fin15AnchoredAtom0325 Fin15AnchoredAtom0335
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1600 at hbad
  cases hcolor0 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13689 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13690 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13691 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13692 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0326 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause13695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0326 Fin15AnchoredAtom0327 Fin15AnchoredAtom0330
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1601 at hbad
  cases hcolor0 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
