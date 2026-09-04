module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 068. -/

theorem fin15Anchored_clause08704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 Fin15AnchoredAtom0940 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 Fin15AnchoredAtom0940 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 Fin15AnchoredAtom0940 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 Fin15AnchoredAtom0940 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08708 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0941 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08709 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0941 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08710 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0941 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08711 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0941 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0941 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0941 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0941 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0291 chi ∧
      Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0941 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0291 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0116 Fin15AnchoredAtom0125
    Fin15AnchoredAtom0291 Fin15AnchoredAtom0941 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08717 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0942 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08718 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0942 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0942 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08720 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0942 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0942 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0942 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0292 chi ∧
      Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0942 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0292 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0117 Fin15AnchoredAtom0126
    Fin15AnchoredAtom0292 Fin15AnchoredAtom0942 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0943 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08726 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0943 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08727 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0943 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08728 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0943 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0943 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0943 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0943 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0293 chi ∧
      Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0943 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0293 chi ∧
      ¬Fin15AnchoredAtom0943 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0118 Fin15AnchoredAtom0127
    Fin15AnchoredAtom0293 Fin15AnchoredAtom0943 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08734 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08735 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08737 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08738 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0294 chi ∧
      Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0294 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0119 Fin15AnchoredAtom0128
    Fin15AnchoredAtom0294 Fin15AnchoredAtom0944 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08744 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08745 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08746 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08747 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0295 chi ∧
      Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0295 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0120 Fin15AnchoredAtom0129
    Fin15AnchoredAtom0295 Fin15AnchoredAtom0945 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08755 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0946 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 Fin15AnchoredAtom0946 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0296 chi ∧
      Fin15AnchoredAtom0946 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 Fin15AnchoredAtom0946 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0296 chi ∧
      ¬Fin15AnchoredAtom0946 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0121 Fin15AnchoredAtom0130
    Fin15AnchoredAtom0296 Fin15AnchoredAtom0946 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08758 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08759 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08760 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08761 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08762 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0297 chi ∧
      Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0297 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0122 Fin15AnchoredAtom0131
    Fin15AnchoredAtom0297 Fin15AnchoredAtom0947 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08768 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08769 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08770 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08771 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08772 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      ¬Fin15AnchoredAtom0298 chi ∧
      Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0132 chi ∧
      Fin15AnchoredAtom0298 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0123 Fin15AnchoredAtom0132
    Fin15AnchoredAtom0298 Fin15AnchoredAtom0948 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08778 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08779 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08780 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08781 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      ¬Fin15AnchoredAtom0299 chi ∧
      Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0133 chi ∧
      Fin15AnchoredAtom0299 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0115 Fin15AnchoredAtom0124 Fin15AnchoredAtom0133
    Fin15AnchoredAtom0299 Fin15AnchoredAtom0949 at hbad
  cases hcolor0 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0950 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08789 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0950 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08790 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0950 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08791 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0950 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0950 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0950 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0950 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0300 chi ∧
      Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0950 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0300 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0117 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0300 Fin15AnchoredAtom0950 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08797 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08798 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08799 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08801 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08802 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0301 chi ∧
      Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0301 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0118 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0301 Fin15AnchoredAtom0951 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08807 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0952 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08808 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0952 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08809 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0952 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08810 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0952 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0952 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0952 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0302 chi ∧
      Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0952 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0302 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0119 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0302 Fin15AnchoredAtom0952 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08815 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08816 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08817 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08818 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08819 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0303 chi ∧
      Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0303 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0120 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0303 Fin15AnchoredAtom0953 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08825 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0954 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0121 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0304 Fin15AnchoredAtom0954 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08826 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0954 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0121 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0304 Fin15AnchoredAtom0954 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0304 chi ∧
      Fin15AnchoredAtom0954 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0121 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0304 Fin15AnchoredAtom0954 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0304 chi ∧
      ¬Fin15AnchoredAtom0954 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0121 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0304 Fin15AnchoredAtom0954 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08829 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08831 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0305 chi ∧
      Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0116 Fin15AnchoredAtom0122 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0305 Fin15AnchoredAtom0955 at hbad
  cases hcolor0 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
