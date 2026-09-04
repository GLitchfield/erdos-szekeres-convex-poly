module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 100. -/

theorem fin15Anchored_clause12800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1497 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12801 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1497 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1497 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1497 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1497 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0306 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0298 Fin15AnchoredAtom0306
    Fin15AnchoredAtom0342 Fin15AnchoredAtom1497 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12807 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12808 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12809 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12810 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0307 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0299 Fin15AnchoredAtom0307
    Fin15AnchoredAtom0343 Fin15AnchoredAtom1498 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12817 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12818 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12819 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12820 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12821 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      ¬Fin15AnchoredAtom0344 chi ∧
      Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0308 chi ∧
      Fin15AnchoredAtom0344 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0293 Fin15AnchoredAtom0308
    Fin15AnchoredAtom0344 Fin15AnchoredAtom1499 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12827 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1500 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12828 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1500 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12829 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1500 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1500 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1500 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1500 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1500 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      ¬Fin15AnchoredAtom0345 chi ∧
      Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1500 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0309 chi ∧
      Fin15AnchoredAtom0345 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0294 Fin15AnchoredAtom0309
    Fin15AnchoredAtom0345 Fin15AnchoredAtom1500 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12836 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12837 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12838 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12839 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12842 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      ¬Fin15AnchoredAtom0346 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0310 chi ∧
      Fin15AnchoredAtom0346 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0295 Fin15AnchoredAtom0310
    Fin15AnchoredAtom0346 Fin15AnchoredAtom1501 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12847 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12848 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12849 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12850 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12851 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0311 chi ∧
      Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0311 chi ∧
      ¬Fin15AnchoredAtom0347 chi ∧
      Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0296 Fin15AnchoredAtom0311
    Fin15AnchoredAtom0347 Fin15AnchoredAtom1502 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12857 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12858 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12859 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12860 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12861 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      ¬Fin15AnchoredAtom0348 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0312 chi ∧
      Fin15AnchoredAtom0348 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0297 Fin15AnchoredAtom0312
    Fin15AnchoredAtom0348 Fin15AnchoredAtom1503 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12867 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12868 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12869 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12870 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12871 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12872 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      ¬Fin15AnchoredAtom0349 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0313 chi ∧
      Fin15AnchoredAtom0349 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0298 Fin15AnchoredAtom0313
    Fin15AnchoredAtom0349 Fin15AnchoredAtom1504 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12879 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12880 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12882 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      ¬Fin15AnchoredAtom0350 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0314 chi ∧
      Fin15AnchoredAtom0350 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0292 Fin15AnchoredAtom0299 Fin15AnchoredAtom0314
    Fin15AnchoredAtom0350 Fin15AnchoredAtom1505 at hbad
  cases hcolor0 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12889 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1506 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12890 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1506 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12891 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1506 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12892 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1506 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12893 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1506 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1506 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1506 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      ¬Fin15AnchoredAtom0351 chi ∧
      Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1506 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0315 chi ∧
      Fin15AnchoredAtom0351 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0294 Fin15AnchoredAtom0315
    Fin15AnchoredAtom0351 Fin15AnchoredAtom1506 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12898 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12899 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12900 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12901 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12902 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0316 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0295 Fin15AnchoredAtom0316
    Fin15AnchoredAtom0352 Fin15AnchoredAtom1507 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12909 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1509 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12910 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1509 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12911 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1509 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12912 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1509 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1509 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1509 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1509 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1509 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0318 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0297 Fin15AnchoredAtom0318
    Fin15AnchoredAtom0354 Fin15AnchoredAtom1509 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12918 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1510 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12919 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1510 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12920 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1510 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12921 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1510 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1510 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1510 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1510 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1510 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0319 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0298 Fin15AnchoredAtom0319
    Fin15AnchoredAtom0355 Fin15AnchoredAtom1510 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12927 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0293 Fin15AnchoredAtom0299 Fin15AnchoredAtom0320
    Fin15AnchoredAtom0356 Fin15AnchoredAtom1511 at hbad
  cases hcolor0 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
