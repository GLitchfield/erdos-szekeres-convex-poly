module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 099. -/

theorem fin15Anchored_clause12672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0447 chi ∧
      Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0283 Fin15AnchoredAtom0286
    Fin15AnchoredAtom0447 Fin15AnchoredAtom1482 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
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

theorem fin15Anchored_clause12674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
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

theorem fin15Anchored_clause12675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
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

theorem fin15Anchored_clause12676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0283 chi ∧
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

theorem fin15Anchored_clause12677 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0284 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1483 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12678 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0448 chi ∧
      Fin15AnchoredAtom1483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0284 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1483 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0281 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0448 chi ∧
      ¬Fin15AnchoredAtom1483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0281 Fin15AnchoredAtom0284 Fin15AnchoredAtom0287
    Fin15AnchoredAtom0448 Fin15AnchoredAtom1483 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12680 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12681 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12683 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12684 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12685 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0449 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0449 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0283 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0449 Fin15AnchoredAtom1484 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12692 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12695 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12696 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12697 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0450 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0450 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0282 Fin15AnchoredAtom0284 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0450 Fin15AnchoredAtom1485 at hbad
  cases hcolor0 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12704 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1486 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12705 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1486 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12706 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1486 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1486 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1486 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1486 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1486 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0451 chi ∧
      Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1486 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0451 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0283 Fin15AnchoredAtom0284 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0451 Fin15AnchoredAtom1486 at hbad
  cases hcolor0 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12713 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1487 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12714 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1487 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12715 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1487 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12716 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1487 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1487 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1487 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0452 chi ∧
      Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1487 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0452 chi ∧
      ¬Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0286 Fin15AnchoredAtom0288
    Fin15AnchoredAtom0452 Fin15AnchoredAtom1487 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12721 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1488 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12722 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      ¬Fin15AnchoredAtom1488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1488 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12723 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1488 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1488 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0453 chi ∧
      Fin15AnchoredAtom1488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0285 Fin15AnchoredAtom0287 Fin15AnchoredAtom0289
    Fin15AnchoredAtom0453 Fin15AnchoredAtom1488 at hbad
  cases hcolor0 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12726 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0286 Fin15AnchoredAtom0287 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1489 at hbad
  cases hcolor0 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0454 chi ∧
      ¬Fin15AnchoredAtom1489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0286 Fin15AnchoredAtom0287 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0454 Fin15AnchoredAtom1489 at hbad
  cases hcolor0 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12728 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12729 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12730 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12732 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12736 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0455 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0455 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0288 Fin15AnchoredAtom0289 Fin15AnchoredAtom0290
    Fin15AnchoredAtom0455 Fin15AnchoredAtom1490 at hbad
  cases hcolor0 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12739 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1491 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12740 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1491 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12741 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1491 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1491 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12743 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1491 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1491 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1491 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1491 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0292 Fin15AnchoredAtom0300
    Fin15AnchoredAtom0336 Fin15AnchoredAtom1491 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1492 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1492 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12750 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1492 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12751 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1492 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1492 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1492 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1492 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0293 Fin15AnchoredAtom0301
    Fin15AnchoredAtom0337 Fin15AnchoredAtom1492 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12756 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1493 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12757 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1493 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12758 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1493 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12759 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1493 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12760 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1493 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1493 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1493 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1493 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0294 Fin15AnchoredAtom0302
    Fin15AnchoredAtom0338 Fin15AnchoredAtom1493 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12765 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12766 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12767 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12768 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12769 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12770 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12771 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0295 Fin15AnchoredAtom0303
    Fin15AnchoredAtom0339 Fin15AnchoredAtom1494 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12777 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12778 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12779 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12780 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12781 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0296 Fin15AnchoredAtom0304
    Fin15AnchoredAtom0340 Fin15AnchoredAtom1495 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12787 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1496 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1496 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12789 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1496 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12790 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1496 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12791 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1496 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1496 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1496 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1496 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0291 Fin15AnchoredAtom0297 Fin15AnchoredAtom0305
    Fin15AnchoredAtom0341 Fin15AnchoredAtom1496 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause12796 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
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

theorem fin15Anchored_clause12797 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0306 chi ∧
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

theorem fin15Anchored_clause12798 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
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

theorem fin15Anchored_clause12799 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
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

end ErdosSzekeres

end
