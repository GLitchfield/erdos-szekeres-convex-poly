module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 070. -/

theorem fin15Anchored_clause08960 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0124 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0970 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08961 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0124 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0970 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08962 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0124 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0970 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08963 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0124 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0970 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08964 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0124 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0970 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08965 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0124 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0970 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0124 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0970 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0320 chi ∧
      Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0124 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0970 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0320 chi ∧
      ¬Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0118 Fin15AnchoredAtom0124 Fin15AnchoredAtom0154
    Fin15AnchoredAtom0320 Fin15AnchoredAtom0970 at hbad
  cases hcolor0 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08969 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0120 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0971 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08970 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0120 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0971 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08971 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0120 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0971 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08972 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0120 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0971 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0120 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0971 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0120 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0971 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0120 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0971 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0321 chi ∧
      Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0120 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0971 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0321 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0120 Fin15AnchoredAtom0155
    Fin15AnchoredAtom0321 Fin15AnchoredAtom0971 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0121 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0322 Fin15AnchoredAtom0972 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08979 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0121 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0322 Fin15AnchoredAtom0972 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08980 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0121 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0322 Fin15AnchoredAtom0972 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0121 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0322 Fin15AnchoredAtom0972 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0121 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0322 Fin15AnchoredAtom0972 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0322 chi ∧
      Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0121 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0322 Fin15AnchoredAtom0972 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0322 chi ∧
      ¬Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0121 Fin15AnchoredAtom0156
    Fin15AnchoredAtom0322 Fin15AnchoredAtom0972 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08985 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0122 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0973 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08986 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0122 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0973 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08987 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0122 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0973 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08988 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0122 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0973 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0122 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0973 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0122 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0973 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0122 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0973 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0323 chi ∧
      Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0122 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0973 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0323 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0122 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0323 Fin15AnchoredAtom0973 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0974 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08995 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0974 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08996 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0974 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08997 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0974 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0974 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0974 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi ∧
      Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0974 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 Fin15AnchoredAtom0974 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09002 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09003 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09004 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09005 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09006 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi ∧
      Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 Fin15AnchoredAtom0975 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi ∧
      ¬Fin15AnchoredAtom0976 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0121 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0326 Fin15AnchoredAtom0976 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0977 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09014 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0977 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09015 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0977 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09016 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0977 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0977 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0977 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi ∧
      Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0977 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 Fin15AnchoredAtom0977 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09021 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0978 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09022 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0978 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09023 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0978 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09024 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0978 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0978 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0978 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi ∧
      Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0978 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 Fin15AnchoredAtom0978 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09029 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0979 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09030 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0979 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09031 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0979 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09032 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0979 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0979 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0979 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi ∧
      Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0979 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 Fin15AnchoredAtom0979 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09037 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 Fin15AnchoredAtom0980 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09038 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 Fin15AnchoredAtom0980 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09039 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 Fin15AnchoredAtom0980 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09040 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 Fin15AnchoredAtom0980 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 Fin15AnchoredAtom0980 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi ∧
      ¬Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 Fin15AnchoredAtom0980 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09043 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0981 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 Fin15AnchoredAtom0981 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09044 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0331 chi ∧
      Fin15AnchoredAtom0981 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 Fin15AnchoredAtom0981 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi ∧
      ¬Fin15AnchoredAtom0981 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 Fin15AnchoredAtom0981 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09046 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0332 chi ∧
      Fin15AnchoredAtom0982 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0124 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0332 Fin15AnchoredAtom0982 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09047 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0983 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09048 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0983 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09049 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0983 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09050 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0983 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0983 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0983 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi ∧
      Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0983 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 Fin15AnchoredAtom0983 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09055 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0984 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09056 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0984 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09057 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0984 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09058 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0984 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0984 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0984 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0984 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi ∧
      Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0984 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi ∧
      ¬Fin15AnchoredAtom0984 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 Fin15AnchoredAtom0984 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09064 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0985 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09065 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0985 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09066 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0985 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09067 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0985 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0985 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0985 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi ∧
      Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0985 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi ∧
      ¬Fin15AnchoredAtom0985 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 Fin15AnchoredAtom0985 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09072 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09073 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09074 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09075 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi ∧
      Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi ∧
      ¬Fin15AnchoredAtom0986 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 Fin15AnchoredAtom0986 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09082 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0987 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09083 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0987 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09084 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0987 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09085 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0987 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09086 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0987 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause09087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0987 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 Fin15AnchoredAtom0987 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
