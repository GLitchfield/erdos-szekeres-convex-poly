module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 015. -/

theorem fin15Anchored_clause01920 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01921 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0433 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0153 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0433 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01922 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01923 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01924 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01925 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01926 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01927 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01928 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0152 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01929 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0152 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0434 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0152 Fin15AnchoredAtom0154 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0434 at hbad
  cases hcolor0 : chi ⟨1, 8, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01930 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01931 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01932 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01933 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01934 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01935 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01936 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0153 chi ∧
      ¬Fin15AnchoredAtom0154 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01937 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0153 chi ∧
      Fin15AnchoredAtom0154 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0435 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 8) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0153 Fin15AnchoredAtom0154 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0435 at hbad
  cases hcolor0 : chi ⟨1, 8, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 8, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01938 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01939 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01940 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01941 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01942 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01943 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01944 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01945 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0436 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0156 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0436 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01946 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01947 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01948 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01949 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01950 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01951 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01952 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01953 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0157 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01954 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01955 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01956 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01957 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01958 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01959 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01960 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01961 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0158 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01962 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01963 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01964 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01965 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01966 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01967 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01968 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01969 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0155 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0155 Fin15AnchoredAtom0159 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨1, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01970 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01971 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01972 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01973 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01974 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01975 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01976 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01977 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0157 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01978 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0158 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01979 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0158 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01980 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0158 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01981 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0158 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01982 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0158 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01983 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0158 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01984 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0158 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01985 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0159 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01986 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0159 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01987 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0159 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01988 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0159 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01989 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0159 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01990 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0156 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0156 Fin15AnchoredAtom0159 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨1, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01991 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01992 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01993 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01994 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01995 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01996 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01997 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01998 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0158 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01999 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02000 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02001 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02002 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02003 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02004 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02005 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0157 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02006 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0157 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0157 Fin15AnchoredAtom0159 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨1, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02007 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02008 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02009 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02010 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02011 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02012 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02013 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02014 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0158 Fin15AnchoredAtom0159 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02015 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02016 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02017 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02018 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02019 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02020 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02021 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02022 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0161 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02023 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02024 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02025 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02026 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02027 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02028 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02029 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02030 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0162 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02031 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0163 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02032 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0163 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02033 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0163 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02034 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0163 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02035 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0160 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0160 Fin15AnchoredAtom0163 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02036 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02037 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02038 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02039 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02040 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02041 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02042 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02043 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0161 Fin15AnchoredAtom0162 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02044 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0161 chi ∧
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

theorem fin15Anchored_clause02045 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
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

theorem fin15Anchored_clause02046 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0161 chi ∧
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

theorem fin15Anchored_clause02047 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0163 chi ∧
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

end ErdosSzekeres

end
