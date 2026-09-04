module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 025. -/

theorem fin15Anchored_clause03200 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0204 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03201 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03202 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03203 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03204 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03205 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03206 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03207 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03208 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0205 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03209 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03210 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03211 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03212 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03213 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03214 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03215 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03216 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0206 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03217 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03218 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03219 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03220 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03221 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03222 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03223 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03224 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0203 Fin15AnchoredAtom0207 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03225 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03226 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03227 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03228 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03229 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03230 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03231 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03232 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0205 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03233 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03234 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03235 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03236 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03237 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03238 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03239 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03240 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0206 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03241 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03242 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03243 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03244 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03245 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0232 chi ∧
      Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0204 Fin15AnchoredAtom0207 Fin15AnchoredAtom0232
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03246 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03247 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03248 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03249 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03250 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03251 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03252 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03253 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0206 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03254 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03255 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03256 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03257 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03258 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03259 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03260 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03261 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0205 Fin15AnchoredAtom0207 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03262 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03263 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03264 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03265 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03266 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03267 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03268 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03269 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0399 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0206 Fin15AnchoredAtom0207 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0399 at hbad
  cases hcolor0 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03270 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03271 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03272 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03273 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03274 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03275 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03276 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0400 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0209 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0400 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03277 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03278 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03279 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03280 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03281 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03282 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03283 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03284 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0401 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0210 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0401 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03285 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0212 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03286 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0212 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03287 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0212 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03288 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0212 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03289 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0403 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0212 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0403 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03290 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03291 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03292 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03293 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03294 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03295 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03296 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03297 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0404 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0213 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0404 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03298 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0214 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03299 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0214 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03300 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0214 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03301 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0405 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0208 Fin15AnchoredAtom0214 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0405 at hbad
  cases hcolor0 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03302 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03303 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03304 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03305 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03306 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03307 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03308 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03309 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0406 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0210 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0406 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03310 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03311 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03312 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03313 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03314 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03315 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03316 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03317 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0407 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0211 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0407 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03318 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03319 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03320 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03321 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03322 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03323 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03324 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03325 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0408 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0212 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0408 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03326 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03327 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0409 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 7) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0209 Fin15AnchoredAtom0213 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0409 at hbad
  cases hcolor0 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
