module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 098. -/

theorem fin15Anchored_clause12544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1464 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1464 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1464 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1464 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0271 Fin15AnchoredAtom0275 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1464 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12549 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1468 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12550 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1468 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12551 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1468 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1468 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1468 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1468 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1468 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1468 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0274 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1468 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1469 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12559 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1469 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12560 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1469 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12561 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1469 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12562 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1469 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1469 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1469 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1469 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0273 Fin15AnchoredAtom0275 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1469 at hbad
  cases hcolor0 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12567 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12568 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12569 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12570 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0274 Fin15AnchoredAtom0275 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1470 at hbad
  cases hcolor0 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12577 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1471 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1471 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12579 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1471 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12580 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1471 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1471 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1471 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1471 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1471 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0277 Fin15AnchoredAtom0281
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1471 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12586 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1472 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12587 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1472 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12588 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1472 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12589 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1472 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1472 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1472 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1472 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1472 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0278 Fin15AnchoredAtom0282
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1472 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12595 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12597 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12598 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12599 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0279 Fin15AnchoredAtom0283
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1473 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12605 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12608 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12609 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0439 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0439 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0276 Fin15AnchoredAtom0280 Fin15AnchoredAtom0284
    Fin15AnchoredAtom0439 Fin15AnchoredAtom1474 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12616 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1475 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12617 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1475 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12618 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1475 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1475 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0440 chi ∧
      ¬Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0278 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0440 Fin15AnchoredAtom1475 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12621 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1476 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12622 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0441 chi ∧
      Fin15AnchoredAtom1476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1476 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0441 chi ∧
      ¬Fin15AnchoredAtom1476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0279 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0441 Fin15AnchoredAtom1476 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12624 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1477 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12625 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1477 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12626 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1477 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      Fin15AnchoredAtom1477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1477 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0442 chi ∧
      ¬Fin15AnchoredAtom1477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0277 Fin15AnchoredAtom0280 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0442 Fin15AnchoredAtom1477 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12629 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12631 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12632 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12633 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0443 chi ∧
      Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0443 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0279 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0443 Fin15AnchoredAtom1478 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12640 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12641 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12642 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12643 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0444 chi ∧
      Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0444 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0278 Fin15AnchoredAtom0280 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0444 Fin15AnchoredAtom1479 at hbad
  cases hcolor0 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12649 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1480 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12650 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1480 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12651 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1480 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12652 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1480 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12653 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1480 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1480 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1480 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0445 chi ∧
      Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1480 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0445 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0279 Fin15AnchoredAtom0280 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0445 Fin15AnchoredAtom1480 at hbad
  cases hcolor0 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12658 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12659 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12660 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12661 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12662 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0446 chi ∧
      Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0446 chi ∧
      ¬Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0282 Fin15AnchoredAtom0285
    Fin15AnchoredAtom0446 Fin15AnchoredAtom1481 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12668 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1482 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12669 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1482 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12670 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      ¬Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1482 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12671 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1482 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
