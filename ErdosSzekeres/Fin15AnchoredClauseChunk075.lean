module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 075. -/

theorem fin15Anchored_clause09600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0144 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1051 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0401 chi ∧
      Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0144 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1051 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0401 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0144 Fin15AnchoredAtom0150
    Fin15AnchoredAtom0401 Fin15AnchoredAtom1051 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09603 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09605 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09608 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0403 chi ∧
      Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0403 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0146 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0403 Fin15AnchoredAtom1053 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09613 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0147 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1054 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09614 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0147 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1054 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09615 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0147 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1054 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09616 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0147 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1054 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0147 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1054 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0147 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1054 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0147 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1054 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0404 chi ∧
      Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0147 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1054 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0404 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0147 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0404 Fin15AnchoredAtom1054 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09622 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0148 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1055 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09623 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0148 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1055 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09624 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0148 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1055 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09625 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0148 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1055 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0148 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1055 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0405 chi ∧
      Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0148 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1055 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0142 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0405 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0142 Fin15AnchoredAtom0148 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0405 Fin15AnchoredAtom1055 at hbad
  cases hcolor0 : chi ⟨1, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09629 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09631 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09632 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09633 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0406 chi ∧
      Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0406 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0144 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0406 Fin15AnchoredAtom1056 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0145 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1057 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09640 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0145 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1057 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09641 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      Fin15AnchoredAtom1057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0145 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1057 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0145 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1057 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0407 chi ∧
      ¬Fin15AnchoredAtom1057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0145 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0407 Fin15AnchoredAtom1057 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09644 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0146 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1058 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09645 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0146 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1058 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09646 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0146 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1058 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09647 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0146 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1058 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0146 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1058 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0146 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1058 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0146 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1058 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0408 chi ∧
      Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0146 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1058 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0408 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0146 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0408 Fin15AnchoredAtom1058 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09653 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09654 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09655 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09656 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09657 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0409 chi ∧
      Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0409 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0147 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0409 Fin15AnchoredAtom1059 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09663 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0148 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1060 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09664 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0148 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1060 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09665 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0148 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1060 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09666 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0148 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1060 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0148 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1060 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0148 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1060 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0410 chi ∧
      Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0148 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1060 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0143 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0410 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0143 Fin15AnchoredAtom0148 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0410 Fin15AnchoredAtom1060 at hbad
  cases hcolor0 : chi ⟨1, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09671 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0145 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1061 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09672 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0145 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1061 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0145 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1061 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0145 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1061 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0145 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1061 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0145 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1061 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0411 chi ∧
      Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0145 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1061 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0411 chi ∧
      ¬Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0145 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0411 Fin15AnchoredAtom1061 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09679 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1062 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09680 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1062 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09681 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1062 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1062 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1062 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1062 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1062 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0412 chi ∧
      Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1062 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0412 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0146 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0412 Fin15AnchoredAtom1062 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09689 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09690 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09691 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09692 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0413 chi ∧
      Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0413 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0147 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0413 Fin15AnchoredAtom1063 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09698 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1064 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1064 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09700 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1064 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09701 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1064 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09702 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1064 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1064 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1064 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0414 chi ∧
      Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1064 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0144 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0414 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0144 Fin15AnchoredAtom0148 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0414 Fin15AnchoredAtom1064 at hbad
  cases hcolor0 : chi ⟨1, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1065 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09708 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1065 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09709 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1065 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1065 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1065 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1065 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0415 chi ∧
      ¬Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0146 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0415 Fin15AnchoredAtom1065 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09714 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1066 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1066 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1066 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1066 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      Fin15AnchoredAtom1066 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1066 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0416 chi ∧
      ¬Fin15AnchoredAtom1066 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0147 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0416 Fin15AnchoredAtom1066 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09718 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0145 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1067 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1067 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      ¬Fin15AnchoredAtom1067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1067 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0145 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0417 chi ∧
      Fin15AnchoredAtom1067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0145 Fin15AnchoredAtom0148 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0417 Fin15AnchoredAtom1067 at hbad
  cases hcolor0 : chi ⟨1, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09722 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1068 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09723 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1068 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09724 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1068 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1068 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09726 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1068 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0418 chi ∧
      Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0147 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0418 Fin15AnchoredAtom1068 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
