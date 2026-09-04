module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 048. -/

theorem fin15Anchored_clause06144 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06145 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06146 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0437 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0359 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0437 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06147 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06148 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06149 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06150 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06151 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06152 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06153 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06154 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0438 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0360 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0438 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06155 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06156 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06157 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06158 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06159 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06160 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06161 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06162 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0439 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0357 Fin15AnchoredAtom0361 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0439 at hbad
  cases hcolor0 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06163 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06164 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06165 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06166 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06167 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06168 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06169 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06170 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0440 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0359 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0440 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06171 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06172 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06173 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06174 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06175 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06176 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06177 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06178 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0441 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0360 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0441 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06179 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0361 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06180 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0361 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06181 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0361 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06182 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0361 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06183 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0442 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0358 Fin15AnchoredAtom0361 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0442 at hbad
  cases hcolor0 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06184 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06185 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06186 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06187 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06188 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06189 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06190 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06191 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0443 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0360 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0443 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06192 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06193 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06194 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06195 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06196 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06197 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06198 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06199 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0444 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0359 Fin15AnchoredAtom0361 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0444 at hbad
  cases hcolor0 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06200 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06201 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06202 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06203 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06204 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06205 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06206 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06207 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0445 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 9) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0360 Fin15AnchoredAtom0361 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0445 at hbad
  cases hcolor0 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06208 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06209 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06210 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06211 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06212 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06213 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06214 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06215 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0446 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0363 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0446 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06216 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06217 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06218 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06219 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06220 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06221 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06222 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06223 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0447 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0364 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0447 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06224 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06225 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06226 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06227 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06228 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0448 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0362 Fin15AnchoredAtom0365 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0448 at hbad
  cases hcolor0 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06229 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06230 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06231 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06232 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06233 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06234 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06235 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06236 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0449 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0364 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0449 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06237 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06238 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06239 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06240 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06241 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06242 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06243 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06244 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0450 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0363 Fin15AnchoredAtom0365 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0450 at hbad
  cases hcolor0 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06245 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06246 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06247 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06248 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06249 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06250 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06251 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06252 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0451 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 10) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0364 Fin15AnchoredAtom0365 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0451 at hbad
  cases hcolor0 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06253 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06254 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06255 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06256 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06257 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06258 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06259 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06260 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0452 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0367 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0452 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06261 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06262 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06263 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06264 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06265 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06266 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06267 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06268 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0453 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0366 Fin15AnchoredAtom0368 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0453 at hbad
  cases hcolor0 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06269 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06270 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      ¬Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause06271 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0371 chi ∧
      Fin15AnchoredAtom0454 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 11) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0367 Fin15AnchoredAtom0368 Fin15AnchoredAtom0371
    Fin15AnchoredAtom0454 at hbad
  cases hcolor0 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨11, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
