module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 066. -/

theorem fin15Anchored_clause08448 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0906 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0906 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0906 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0906 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0108 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0256 Fin15AnchoredAtom0906 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08453 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0907 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08454 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0907 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08455 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0907 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08456 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0907 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0907 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0907 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0907 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0109 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0257 Fin15AnchoredAtom0907 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08461 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08463 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08464 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08465 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08466 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0110 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0258 Fin15AnchoredAtom0908 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08473 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0909 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 Fin15AnchoredAtom0909 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0909 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 Fin15AnchoredAtom0909 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0909 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0111 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0259 Fin15AnchoredAtom0909 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08476 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08477 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08478 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08479 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08480 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0112 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0260 Fin15AnchoredAtom0910 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0911 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08487 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0911 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08488 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0911 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08489 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0911 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0911 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0911 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0911 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0911 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0140 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0113 Fin15AnchoredAtom0140
    Fin15AnchoredAtom0261 Fin15AnchoredAtom0911 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08495 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0912 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08496 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0912 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08497 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0912 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08498 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0912 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0912 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0912 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0912 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0141 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0106 Fin15AnchoredAtom0114 Fin15AnchoredAtom0141
    Fin15AnchoredAtom0262 Fin15AnchoredAtom0912 at hbad
  cases hcolor0 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08503 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08504 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08505 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08506 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08507 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0108 Fin15AnchoredAtom0142
    Fin15AnchoredAtom0263 Fin15AnchoredAtom0913 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08513 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0914 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08514 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0914 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08515 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0914 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08516 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0914 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0914 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0914 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0914 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0914 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0109 Fin15AnchoredAtom0143
    Fin15AnchoredAtom0264 Fin15AnchoredAtom0914 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08522 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0915 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08523 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0915 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08524 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0915 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08525 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0915 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08526 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0915 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0915 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0915 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0915 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0110 Fin15AnchoredAtom0144
    Fin15AnchoredAtom0265 Fin15AnchoredAtom0915 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0916 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0111 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0266 Fin15AnchoredAtom0916 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0916 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0111 Fin15AnchoredAtom0145
    Fin15AnchoredAtom0266 Fin15AnchoredAtom0916 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08533 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0917 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08534 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0917 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08535 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0917 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08536 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0917 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08537 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0917 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0917 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0917 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0917 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0112 Fin15AnchoredAtom0146
    Fin15AnchoredAtom0267 Fin15AnchoredAtom0917 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08542 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08543 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08544 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08545 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0113 Fin15AnchoredAtom0147
    Fin15AnchoredAtom0268 Fin15AnchoredAtom0918 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08553 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08554 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08555 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08556 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0107 Fin15AnchoredAtom0114 Fin15AnchoredAtom0148
    Fin15AnchoredAtom0269 Fin15AnchoredAtom0919 at hbad
  cases hcolor0 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08562 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0920 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08563 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0920 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08564 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0920 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08565 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0920 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0920 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0920 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0920 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0920 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0109 Fin15AnchoredAtom0149
    Fin15AnchoredAtom0270 Fin15AnchoredAtom0920 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08571 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 Fin15AnchoredAtom0921 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08572 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 Fin15AnchoredAtom0921 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08573 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 Fin15AnchoredAtom0921 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08574 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 Fin15AnchoredAtom0921 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08575 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0110 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0271 Fin15AnchoredAtom0921 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
