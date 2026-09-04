module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 067. -/

theorem fin15Anchored_clause08576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
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

theorem fin15Anchored_clause08577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
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

theorem fin15Anchored_clause08578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0150 chi ∧
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

theorem fin15Anchored_clause08579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0110 chi ∧
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

theorem fin15Anchored_clause08580 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0112 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0273 Fin15AnchoredAtom0923 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08581 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0112 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0273 Fin15AnchoredAtom0923 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08582 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0112 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0273 Fin15AnchoredAtom0923 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0112 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0273 Fin15AnchoredAtom0923 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0112 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0273 Fin15AnchoredAtom0923 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0112 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0273 Fin15AnchoredAtom0923 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0112 Fin15AnchoredAtom0152
    Fin15AnchoredAtom0273 Fin15AnchoredAtom0923 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08587 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0113 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0924 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08588 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0113 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0924 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08589 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0113 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0924 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08590 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0113 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0924 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0113 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0924 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0113 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0924 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0113 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0924 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0113 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0924 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0113 Fin15AnchoredAtom0153
    Fin15AnchoredAtom0274 Fin15AnchoredAtom0924 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0114 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0925 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08597 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0114 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0925 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08598 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0114 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0925 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08599 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0114 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0925 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0114 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0925 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0114 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0925 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0275 chi ∧
      Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0114 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0925 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0275 chi ∧
      ¬Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0108 Fin15AnchoredAtom0114 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0275 Fin15AnchoredAtom0925 at hbad
  cases hcolor0 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0110 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0926 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08605 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0110 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0926 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0110 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0926 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08607 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0110 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0926 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0110 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0926 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0110 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0926 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0110 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0926 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0276 chi ∧
      Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0110 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0926 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0276 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0110 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0276 Fin15AnchoredAtom0926 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08613 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0111 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0277 Fin15AnchoredAtom0927 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08614 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      ¬Fin15AnchoredAtom0927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0111 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0277 Fin15AnchoredAtom0927 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08615 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0111 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0277 Fin15AnchoredAtom0927 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0111 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0277 Fin15AnchoredAtom0927 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0111 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0277 Fin15AnchoredAtom0927 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0277 chi ∧
      Fin15AnchoredAtom0927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0111 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0277 Fin15AnchoredAtom0927 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08619 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0112 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0928 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08620 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0112 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0928 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08621 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0112 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0928 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08622 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0112 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0928 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08623 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0112 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0928 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0112 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0928 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0112 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0928 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0278 chi ∧
      Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0112 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0928 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0278 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0112 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0278 Fin15AnchoredAtom0928 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08628 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0113 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0929 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08629 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0113 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0929 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0113 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0929 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08631 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0113 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0929 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0113 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0929 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0113 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0929 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0279 chi ∧
      Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0113 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0929 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0279 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0113 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0279 Fin15AnchoredAtom0929 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08636 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0114 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0930 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08637 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0114 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0930 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08638 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0114 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0930 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0114 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0930 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0114 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0930 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0114 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0930 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0280 chi ∧
      Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0114 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0930 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0280 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0109 Fin15AnchoredAtom0114 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0280 Fin15AnchoredAtom0930 at hbad
  cases hcolor0 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08644 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0281 chi ∧
      ¬Fin15AnchoredAtom0931 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0111 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0281 Fin15AnchoredAtom0931 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08645 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0112 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0932 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08646 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0112 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0932 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08647 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0112 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0932 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08648 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0112 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0932 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0112 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0932 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0112 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0932 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0282 chi ∧
      Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0112 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0932 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0282 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0112 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0282 Fin15AnchoredAtom0932 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08653 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08654 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08655 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08656 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08657 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0283 chi ∧
      Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0283 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0113 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0283 Fin15AnchoredAtom0933 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08663 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0114 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0934 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08664 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0114 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0934 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08665 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0114 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0934 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08666 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0114 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0934 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0114 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0934 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0114 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0934 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0284 chi ∧
      Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0114 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0934 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0110 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0284 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0110 Fin15AnchoredAtom0114 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0284 Fin15AnchoredAtom0934 at hbad
  cases hcolor0 : chi ⟨1, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08671 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0112 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0285 Fin15AnchoredAtom0935 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08672 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      ¬Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0112 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0285 Fin15AnchoredAtom0935 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08673 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0112 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0285 Fin15AnchoredAtom0935 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08674 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0112 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0285 Fin15AnchoredAtom0935 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0285 chi ∧
      Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0112 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0285 Fin15AnchoredAtom0935 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08676 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0936 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0113 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0286 Fin15AnchoredAtom0936 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0286 chi ∧
      Fin15AnchoredAtom0936 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0113 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0286 Fin15AnchoredAtom0936 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0286 chi ∧
      ¬Fin15AnchoredAtom0936 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0113 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0286 Fin15AnchoredAtom0936 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08679 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0111 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0287 chi ∧
      ¬Fin15AnchoredAtom0937 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0114 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0287 Fin15AnchoredAtom0937 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08680 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0937 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0114 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0287 Fin15AnchoredAtom0937 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08681 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0111 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0287 chi ∧
      Fin15AnchoredAtom0937 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0111 Fin15AnchoredAtom0114 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0287 Fin15AnchoredAtom0937 at hbad
  cases hcolor0 : chi ⟨1, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0113 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0938 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08683 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0113 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0938 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08684 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0113 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0938 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08685 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0113 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0938 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0113 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0938 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0113 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0938 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0288 chi ∧
      Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0113 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0938 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0288 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0113 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0288 Fin15AnchoredAtom0938 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08690 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0114 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0939 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08691 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0114 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0939 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08692 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0114 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0939 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0114 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0939 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0114 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0939 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0112 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0114 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0939 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0114 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0939 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0289 chi ∧
      Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0114 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0939 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0112 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0289 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0112 Fin15AnchoredAtom0114 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0289 Fin15AnchoredAtom0939 at hbad
  cases hcolor0 : chi ⟨1, 3, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
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

theorem fin15Anchored_clause08700 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 Fin15AnchoredAtom0940 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08701 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0113 chi ∧
      ¬Fin15AnchoredAtom0114 chi ∧
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

theorem fin15Anchored_clause08702 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0113 chi ∧
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

theorem fin15Anchored_clause08703 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0113 chi ∧
      Fin15AnchoredAtom0114 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0290 chi ∧
      Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0113 Fin15AnchoredAtom0114 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0290 Fin15AnchoredAtom0940 at hbad
  cases hcolor0 : chi ⟨1, 3, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
