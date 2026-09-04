module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 009. -/

theorem fin15Anchored_clause01152 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01153 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01154 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01155 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01156 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      ¬Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01157 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01158 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0158 chi ∧
      Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0123 Fin15AnchoredAtom0158
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01159 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01160 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01161 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01162 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01163 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01164 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      ¬Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01165 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0119 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01166 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0119 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0159 chi ∧
      Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0119 Fin15AnchoredAtom0124 Fin15AnchoredAtom0159
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨1, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01167 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0121 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01168 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0121 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01169 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0121 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01170 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0160 chi ∧
      Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0121 Fin15AnchoredAtom0160
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01171 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01172 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01173 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01174 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01175 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01176 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      ¬Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01177 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01178 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0161 chi ∧
      Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0122 Fin15AnchoredAtom0161
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01179 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01180 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01181 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01182 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01183 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01184 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      ¬Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01185 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01186 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0162 chi ∧
      Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0123 Fin15AnchoredAtom0162
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01187 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01188 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01189 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01190 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01191 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01192 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      ¬Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01193 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01194 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0120 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0163 chi ∧
      Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0120 Fin15AnchoredAtom0124 Fin15AnchoredAtom0163
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨1, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01195 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01196 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01197 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01198 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01199 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01200 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      ¬Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01201 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01202 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0164 chi ∧
      Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0122 Fin15AnchoredAtom0164
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01203 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01204 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01205 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01206 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01207 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      ¬Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01208 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0121 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01209 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0165 chi ∧
      Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0123 Fin15AnchoredAtom0165
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01210 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0332 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0124 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0332 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01211 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0166 chi ∧
      Fin15AnchoredAtom0332 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0124 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0332 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01212 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0121 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0166 chi ∧
      ¬Fin15AnchoredAtom0332 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0121 Fin15AnchoredAtom0124 Fin15AnchoredAtom0166
    Fin15AnchoredAtom0332 at hbad
  cases hcolor0 : chi ⟨1, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01213 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01214 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01215 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01216 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01217 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01218 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      ¬Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01219 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01220 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0167 chi ∧
      Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0123 Fin15AnchoredAtom0167
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01221 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01222 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01223 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01224 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01225 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01226 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      ¬Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01227 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0122 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01228 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0122 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0168 chi ∧
      Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0122 Fin15AnchoredAtom0124 Fin15AnchoredAtom0168
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨1, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01229 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01230 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01231 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01232 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01233 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01234 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      ¬Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01235 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0123 chi ∧
      ¬Fin15AnchoredAtom0124 chi ∧
      Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01236 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0123 chi ∧
      Fin15AnchoredAtom0124 chi ∧
      ¬Fin15AnchoredAtom0169 chi ∧
      Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0123 Fin15AnchoredAtom0124 Fin15AnchoredAtom0169
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨1, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01237 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01238 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01239 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01240 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01241 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01242 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01243 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0126 chi ∧
      Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01244 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0126 chi ∧
      ¬Fin15AnchoredAtom0134 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0126 Fin15AnchoredAtom0134
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01245 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01246 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01247 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01248 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01249 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01250 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01251 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0127 chi ∧
      Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01252 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0127 chi ∧
      ¬Fin15AnchoredAtom0135 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0127 Fin15AnchoredAtom0135
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01253 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01254 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01255 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01256 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01257 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01258 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01259 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0128 chi ∧
      Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01260 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0128 chi ∧
      ¬Fin15AnchoredAtom0136 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0128 Fin15AnchoredAtom0136
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01261 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01262 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01263 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01264 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01265 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01266 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01267 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0129 chi ∧
      Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01268 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0129 chi ∧
      ¬Fin15AnchoredAtom0137 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0129 Fin15AnchoredAtom0137
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01269 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01270 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01271 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01272 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01273 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01274 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01275 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0130 chi ∧
      Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01276 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0130 chi ∧
      ¬Fin15AnchoredAtom0138 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0130 Fin15AnchoredAtom0138
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01277 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      ¬Fin15AnchoredAtom0131 chi ∧
      Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01278 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause01279 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0125 chi ∧
      Fin15AnchoredAtom0131 chi ∧
      ¬Fin15AnchoredAtom0139 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 1) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0125 Fin15AnchoredAtom0131 Fin15AnchoredAtom0139
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨1, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨1, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨1, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
