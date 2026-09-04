module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 076. -/

theorem fin15Anchored_clause09728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
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

theorem fin15Anchored_clause09729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
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

theorem fin15Anchored_clause09730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0146 chi ∧
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

theorem fin15Anchored_clause09731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0147 chi ∧
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

theorem fin15Anchored_clause09732 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1069 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09733 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1069 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09734 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1069 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09735 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1069 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1069 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0146 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1069 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1069 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0419 chi ∧
      Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1069 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0146 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0419 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0146 Fin15AnchoredAtom0148 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0419 Fin15AnchoredAtom1069 at hbad
  cases hcolor0 : chi ⟨1, 7, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09741 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09743 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09744 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09745 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0147 chi ∧
      ¬Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0420 chi ∧
      Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0147 chi ∧
      Fin15AnchoredAtom0148 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0420 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0147 Fin15AnchoredAtom0148 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0420 Fin15AnchoredAtom1070 at hbad
  cases hcolor0 : chi ⟨1, 7, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09752 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09753 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09754 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09755 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0421 chi ∧
      Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0421 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0150 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0421 Fin15AnchoredAtom1071 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09762 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1073 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09763 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1073 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09764 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1073 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09765 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1073 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1073 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1073 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1073 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0423 chi ∧
      Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1073 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0423 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0152 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0423 Fin15AnchoredAtom1073 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09771 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09772 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09773 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09774 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09775 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09776 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0424 chi ∧
      Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0424 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0153 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0424 Fin15AnchoredAtom1074 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09781 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1075 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1075 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09783 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1075 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1075 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1075 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0425 chi ∧
      Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1075 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0149 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0425 chi ∧
      ¬Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0149 Fin15AnchoredAtom0154 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0425 Fin15AnchoredAtom1075 at hbad
  cases hcolor0 : chi ⟨1, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1077 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09789 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1077 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09790 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1077 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09791 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1077 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1077 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1077 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0427 chi ∧
      Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1077 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0427 chi ∧
      ¬Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0152 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0427 Fin15AnchoredAtom1077 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09796 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1078 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09797 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1078 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09798 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1078 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09799 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1078 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1078 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1078 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0428 chi ∧
      Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1078 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0428 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0153 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0428 Fin15AnchoredAtom1078 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09804 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1079 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09805 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1079 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1079 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09807 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1079 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1079 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0429 chi ∧
      Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1079 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0150 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0429 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0150 Fin15AnchoredAtom0154 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0429 Fin15AnchoredAtom1079 at hbad
  cases hcolor0 : chi ⟨1, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09811 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09812 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09813 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09814 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09815 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0433 chi ∧
      Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 Fin15AnchoredAtom1083 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09822 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1084 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09823 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1084 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09824 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1084 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09825 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1084 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1084 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1084 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi ∧
      Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1084 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi ∧
      ¬Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 Fin15AnchoredAtom1084 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1085 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09831 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1085 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09832 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1085 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09833 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1085 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1085 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1085 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1085 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi ∧
      Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1085 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi ∧
      ¬Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 Fin15AnchoredAtom1085 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09839 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1086 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      ¬Fin15AnchoredAtom1086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1086 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1086 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09842 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi ∧
      Fin15AnchoredAtom1086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 Fin15AnchoredAtom1086 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09843 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1087 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09844 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1087 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09845 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1087 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09846 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1087 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09847 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1087 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1087 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1087 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi ∧
      Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1087 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 Fin15AnchoredAtom1087 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09852 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09853 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09854 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09855 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi ∧
      Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 Fin15AnchoredAtom1088 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
