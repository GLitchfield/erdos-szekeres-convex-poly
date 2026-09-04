module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 016. -/

theorem fin15Anchored_clause02048 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02049 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02050 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02051 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0163 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02052 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02053 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02054 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02055 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02056 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02057 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02058 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02059 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0162 Fin15AnchoredAtom0163 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02060 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02061 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02062 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02063 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02064 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02065 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02066 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02067 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0165 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02068 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02069 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02070 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02071 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02072 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02073 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02074 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02075 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0164 Fin15AnchoredAtom0166 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02076 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0165 Fin15AnchoredAtom0166 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02077 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0165 Fin15AnchoredAtom0166 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02078 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0165 Fin15AnchoredAtom0166 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02079 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0165 Fin15AnchoredAtom0166 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02080 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0165 Fin15AnchoredAtom0166 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02081 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02082 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02083 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02084 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02085 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02086 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02087 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02088 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0455 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 12) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0167 Fin15AnchoredAtom0168 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0455 at hbad
  cases hcolor0 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨12, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02089 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02090 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02091 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02092 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02093 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02094 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      ¬Fin15AnchoredAtom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02095 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02096 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0181 chi ∧
      Fin15AnchoredAtom0236 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0171 Fin15AnchoredAtom0181
    Fin15AnchoredAtom0236 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02097 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02098 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02099 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02100 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02101 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02102 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      ¬Fin15AnchoredAtom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02103 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02104 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0182 chi ∧
      Fin15AnchoredAtom0237 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0172 Fin15AnchoredAtom0182
    Fin15AnchoredAtom0237 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02105 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02106 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02107 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02108 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02109 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02110 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      ¬Fin15AnchoredAtom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02111 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02112 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0183 chi ∧
      Fin15AnchoredAtom0238 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0173 Fin15AnchoredAtom0183
    Fin15AnchoredAtom0238 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02113 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0174 Fin15AnchoredAtom0184
    Fin15AnchoredAtom0239 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02114 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0174 Fin15AnchoredAtom0184
    Fin15AnchoredAtom0239 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02115 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0174 Fin15AnchoredAtom0184
    Fin15AnchoredAtom0239 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02116 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0239 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0174 Fin15AnchoredAtom0184
    Fin15AnchoredAtom0239 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02117 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02118 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02119 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02120 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02121 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02122 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02123 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02124 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0240 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0175 Fin15AnchoredAtom0185
    Fin15AnchoredAtom0240 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02125 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02126 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02127 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02128 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02129 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02130 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02131 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02132 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0241 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0176 Fin15AnchoredAtom0186
    Fin15AnchoredAtom0241 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02133 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02134 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02135 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02136 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02137 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02138 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02139 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0242 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0177 Fin15AnchoredAtom0187
    Fin15AnchoredAtom0242 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02140 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02141 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02142 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02143 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02144 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02145 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02146 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02147 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0243 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0178 Fin15AnchoredAtom0188
    Fin15AnchoredAtom0243 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02148 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02149 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02150 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02151 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02152 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02153 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02154 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02155 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0244 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0179 Fin15AnchoredAtom0189
    Fin15AnchoredAtom0244 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02156 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02157 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02158 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02159 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02160 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02161 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02162 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02163 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0170 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0170 Fin15AnchoredAtom0180 Fin15AnchoredAtom0190
    Fin15AnchoredAtom0245 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02164 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02165 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02166 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02167 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02168 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02169 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      ¬Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02170 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02171 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0191 chi ∧
      Fin15AnchoredAtom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0172 Fin15AnchoredAtom0191
    Fin15AnchoredAtom0246 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02172 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02173 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02174 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0192 chi ∧
      Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02175 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
      ¬Fin15AnchoredAtom0247 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0173 Fin15AnchoredAtom0192
    Fin15AnchoredAtom0247 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
