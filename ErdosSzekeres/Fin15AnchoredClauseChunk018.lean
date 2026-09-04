module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 018. -/

theorem fin15Anchored_clause02304 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
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

theorem fin15Anchored_clause02305 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02306 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02307 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02308 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02309 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02310 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02311 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02312 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0175 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0264 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02313 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02314 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02315 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02316 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02317 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02318 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02319 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02320 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0176 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0265 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02321 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02322 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02323 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02324 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02325 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02326 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02327 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02328 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0177 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0266 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02329 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02330 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02331 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02332 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02333 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02334 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02335 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02336 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0178 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0267 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02337 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02338 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02339 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02340 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02341 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02342 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02343 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02344 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0179 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0268 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02345 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02346 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02347 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02348 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02349 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02350 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02351 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02352 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0173 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0173 Fin15AnchoredAtom0180 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0269 at hbad
  cases hcolor0 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02353 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0175 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02354 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0175 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02355 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0175 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02356 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0175 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0270 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02357 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0176 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02358 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0176 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02359 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0176 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02360 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0176 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02361 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0176 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02362 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0176 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02363 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0176 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0271 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02364 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0178 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0273 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02365 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0178 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0273 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02366 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0178 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0273 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02367 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0178 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0273 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02368 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0178 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0273 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02369 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0179 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0274 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02370 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0179 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0274 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02371 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0179 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0274 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02372 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0180 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0275 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02373 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0180 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0275 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02374 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0174 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0180 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0275 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02375 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0174 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0174 Fin15AnchoredAtom0180 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0275 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02376 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02377 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02378 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02379 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02380 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02381 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02382 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02383 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0176 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0276 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02384 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02385 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02386 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02387 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02388 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02389 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02390 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02391 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0177 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0277 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02392 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02393 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02394 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02395 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02396 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02397 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02398 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02399 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0178 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0278 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02400 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02401 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02402 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02403 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02404 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02405 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02406 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0179 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02407 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0179 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0179 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0279 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02408 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02409 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02410 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02411 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02412 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02413 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02414 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      ¬Fin15AnchoredAtom0180 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02415 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0175 chi ∧
      Fin15AnchoredAtom0180 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0175 Fin15AnchoredAtom0180 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0280 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02416 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02417 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02418 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02419 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02420 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02421 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02422 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0177 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02423 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0177 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0177 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0281 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02424 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02425 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02426 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02427 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02428 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02429 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02430 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      ¬Fin15AnchoredAtom0178 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02431 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0176 chi ∧
      Fin15AnchoredAtom0178 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0176 Fin15AnchoredAtom0178 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0282 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
