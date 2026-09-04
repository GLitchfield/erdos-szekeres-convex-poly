module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 064. -/

theorem fin15Anchored_clause08192 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0101 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0873 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08193 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0101 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0873 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0101 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0873 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0101 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0873 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0101 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0873 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0101 Fin15AnchoredAtom0157
    Fin15AnchoredAtom0223 Fin15AnchoredAtom0873 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08198 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0102 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0874 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08199 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0102 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0874 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08200 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0102 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0874 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08201 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0102 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0874 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0102 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0874 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0102 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0874 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0102 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0874 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0102 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0224 Fin15AnchoredAtom0874 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08206 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0103 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0875 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08207 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0103 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0875 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0103 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0875 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08209 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0103 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0875 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08210 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0103 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0875 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0103 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0875 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0103 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0875 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0103 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0875 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0098 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0098 Fin15AnchoredAtom0103 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0225 Fin15AnchoredAtom0875 at hbad
  cases hcolor0 : chi ⟨1, 2, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08215 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0876 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0100 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0226 Fin15AnchoredAtom0876 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08216 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0876 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0100 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0226 Fin15AnchoredAtom0876 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0876 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0100 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0226 Fin15AnchoredAtom0876 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0876 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0100 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0226 Fin15AnchoredAtom0876 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08219 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0101 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0877 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08220 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0101 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0877 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08221 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0101 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0877 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08222 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0101 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0877 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08223 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0101 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0877 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0101 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0877 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0101 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0877 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0101 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0877 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0101 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0227 Fin15AnchoredAtom0877 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08228 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0102 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0878 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08229 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0102 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0878 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08230 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0102 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0878 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08231 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0102 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0878 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0102 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0878 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0102 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0878 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0102 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0878 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0102 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0878 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0102 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0228 Fin15AnchoredAtom0878 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0103 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0879 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08238 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0103 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0879 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08239 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0103 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0879 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08240 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0103 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0879 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0103 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0879 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0103 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0879 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0103 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0879 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0103 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0879 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0099 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0099 Fin15AnchoredAtom0103 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0229 Fin15AnchoredAtom0879 at hbad
  cases hcolor0 : chi ⟨1, 2, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08246 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0880 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0101 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0230 Fin15AnchoredAtom0880 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08247 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0880 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0101 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0230 Fin15AnchoredAtom0880 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0880 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0101 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0230 Fin15AnchoredAtom0880 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0880 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0101 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0230 Fin15AnchoredAtom0880 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08250 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0881 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0102 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0231 Fin15AnchoredAtom0881 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08251 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0881 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0102 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0231 Fin15AnchoredAtom0881 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08252 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0882 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0103 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0232 Fin15AnchoredAtom0882 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08253 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0100 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0882 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0103 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0232 Fin15AnchoredAtom0882 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08254 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0882 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0103 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0232 Fin15AnchoredAtom0882 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0100 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0882 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0100 Fin15AnchoredAtom0103 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0232 Fin15AnchoredAtom0882 at hbad
  cases hcolor0 : chi ⟨1, 2, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08256 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0102 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0883 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08257 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0102 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0883 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08258 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0102 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0883 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08259 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0102 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0883 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08260 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0102 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0883 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0102 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0883 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0102 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0883 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0102 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0233 Fin15AnchoredAtom0883 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08264 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0103 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0884 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08265 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0103 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0884 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08266 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0103 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0884 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08267 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0103 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0884 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0101 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0103 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0884 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0103 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0884 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0103 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0884 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0101 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0101 Fin15AnchoredAtom0103 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0234 Fin15AnchoredAtom0884 at hbad
  cases hcolor0 : chi ⟨1, 2, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08272 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0102 Fin15AnchoredAtom0103 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0885 at hbad
  cases hcolor0 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08273 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0102 Fin15AnchoredAtom0103 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0885 at hbad
  cases hcolor0 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08274 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0102 Fin15AnchoredAtom0103 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0885 at hbad
  cases hcolor0 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08275 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0102 Fin15AnchoredAtom0103 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0885 at hbad
  cases hcolor0 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0102 chi ∧
      ¬Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0102 Fin15AnchoredAtom0103 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0885 at hbad
  cases hcolor0 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0102 Fin15AnchoredAtom0103 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0885 at hbad
  cases hcolor0 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0102 Fin15AnchoredAtom0103 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0885 at hbad
  cases hcolor0 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0102 chi ∧
      Fin15AnchoredAtom0103 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0102 Fin15AnchoredAtom0103 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0235 Fin15AnchoredAtom0885 at hbad
  cases hcolor0 : chi ⟨1, 2, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 2, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08280 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0105 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0886 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08281 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0105 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0886 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08282 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0105 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0886 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0105 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0886 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0105 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0886 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0105 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0886 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      ¬Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0105 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0886 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08287 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      ¬Fin15AnchoredAtom0236 chi ∧
      Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0105 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0886 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0105 chi ∧
      Fin15AnchoredAtom0115 chi ∧
      Fin15AnchoredAtom0236 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0105 Fin15AnchoredAtom0115
    Fin15AnchoredAtom0236 Fin15AnchoredAtom0886 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08289 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0106 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0887 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08290 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0106 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0887 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08291 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0106 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0887 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08292 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0106 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0887 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0106 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0887 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      ¬Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0106 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0887 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08295 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      ¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0106 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0887 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08296 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0106 chi ∧
      Fin15AnchoredAtom0116 chi ∧
      Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0106 Fin15AnchoredAtom0116
    Fin15AnchoredAtom0237 Fin15AnchoredAtom0887 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08297 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0107 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0888 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08298 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0107 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0888 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08299 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0107 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0888 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08300 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0107 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0888 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08301 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0107 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0888 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08302 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      ¬Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0107 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0888 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08303 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      ¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0107 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0888 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08304 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0107 chi ∧
      Fin15AnchoredAtom0117 chi ∧
      Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0107 Fin15AnchoredAtom0117
    Fin15AnchoredAtom0238 Fin15AnchoredAtom0888 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08305 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0889 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08306 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0889 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08307 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0889 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08308 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0889 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08309 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0889 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08310 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      ¬Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0889 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08311 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0889 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08312 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0108 chi ∧
      Fin15AnchoredAtom0118 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0108 Fin15AnchoredAtom0118
    Fin15AnchoredAtom0239 Fin15AnchoredAtom0889 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08313 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0890 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08314 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0890 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08315 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0890 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08316 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0890 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08317 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0890 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08318 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      ¬Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0890 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause08319 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom0104 chi ∧
      Fin15AnchoredAtom0109 chi ∧
      ¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0104 Fin15AnchoredAtom0109 Fin15AnchoredAtom0119
    Fin15AnchoredAtom0240 Fin15AnchoredAtom0890 at hbad
  cases hcolor0 : chi ⟨1, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
