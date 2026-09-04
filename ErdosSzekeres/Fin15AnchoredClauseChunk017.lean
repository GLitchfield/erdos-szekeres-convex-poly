module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 017. -/

theorem fin15Anchored_clause02176 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
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

theorem fin15Anchored_clause02177 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
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

theorem fin15Anchored_clause02178 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0192 chi ∧
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

theorem fin15Anchored_clause02179 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
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

theorem fin15Anchored_clause02180 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0174 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02181 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0174 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02182 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0193 chi ∧
      Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0174 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02183 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0174 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02184 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0193 chi ∧
      ¬Fin15AnchoredAtom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0174 Fin15AnchoredAtom0193
    Fin15AnchoredAtom0248 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02185 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02186 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02187 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02188 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02189 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02190 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      ¬Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02191 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02192 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0194 chi ∧
      Fin15AnchoredAtom0249 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0175 Fin15AnchoredAtom0194
    Fin15AnchoredAtom0249 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02193 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02194 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02195 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02196 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02197 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02198 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      ¬Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02199 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02200 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0195 chi ∧
      Fin15AnchoredAtom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0176 Fin15AnchoredAtom0195
    Fin15AnchoredAtom0250 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02201 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02202 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02203 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02204 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02205 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02206 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      ¬Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02207 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02208 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0196 chi ∧
      Fin15AnchoredAtom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0177 Fin15AnchoredAtom0196
    Fin15AnchoredAtom0251 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02209 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02210 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02211 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02212 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02213 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02214 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      ¬Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02215 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02216 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0197 chi ∧
      Fin15AnchoredAtom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0178 Fin15AnchoredAtom0197
    Fin15AnchoredAtom0252 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02217 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02218 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02219 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02220 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02221 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02222 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02223 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02224 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0179 Fin15AnchoredAtom0198
    Fin15AnchoredAtom0253 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02225 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02226 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02227 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02228 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02229 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02230 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02231 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02232 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0171 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 5) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0171 Fin15AnchoredAtom0180 Fin15AnchoredAtom0199
    Fin15AnchoredAtom0254 at hbad
  cases hcolor0 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02233 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02234 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02235 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02236 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02237 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02238 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02239 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02240 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0173 Fin15AnchoredAtom0200
    Fin15AnchoredAtom0255 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02241 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02242 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02243 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02244 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02245 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02246 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02247 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02248 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0174 Fin15AnchoredAtom0201
    Fin15AnchoredAtom0256 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02249 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02250 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02251 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02252 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02253 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02254 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02255 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02256 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0175 Fin15AnchoredAtom0202
    Fin15AnchoredAtom0257 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02257 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02258 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02259 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02260 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02261 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02262 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02263 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02264 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0176 Fin15AnchoredAtom0203
    Fin15AnchoredAtom0258 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02265 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02266 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02267 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02268 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02269 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02270 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02271 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02272 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0177 Fin15AnchoredAtom0204
    Fin15AnchoredAtom0259 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02273 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02274 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02275 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02276 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02277 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02278 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02279 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02280 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0178 Fin15AnchoredAtom0205
    Fin15AnchoredAtom0260 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02281 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02282 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02283 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02284 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02285 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02286 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02287 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02288 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0179 Fin15AnchoredAtom0206
    Fin15AnchoredAtom0261 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02289 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02290 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02291 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02292 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02293 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02294 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02295 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02296 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0172 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0172 Fin15AnchoredAtom0180 Fin15AnchoredAtom0207
    Fin15AnchoredAtom0262 at hbad
  cases hcolor0 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02297 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02298 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02299 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02300 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02301 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02302 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02303 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0174 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0263 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
