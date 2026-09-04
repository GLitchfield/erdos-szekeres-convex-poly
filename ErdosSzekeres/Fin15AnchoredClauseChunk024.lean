module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 024. -/

theorem fin15Anchored_clause03072 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03073 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03074 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0198 chi ∧
      ¬Fin15AnchoredAtom0199 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03075 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0198 chi ∧
      Fin15AnchoredAtom0199 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0371 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 5) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0198 Fin15AnchoredAtom0199 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0371 at hbad
  cases hcolor0 : chi ⟨2, 5, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03076 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03077 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03078 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03079 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03080 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      ¬Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03081 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03082 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0208 chi ∧
      Fin15AnchoredAtom0372 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0201 Fin15AnchoredAtom0208
    Fin15AnchoredAtom0372 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03083 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03084 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03085 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03086 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03087 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03088 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      ¬Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03089 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03090 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0209 chi ∧
      Fin15AnchoredAtom0373 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0202 Fin15AnchoredAtom0209
    Fin15AnchoredAtom0373 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03091 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03092 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03093 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03094 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03095 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03096 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      ¬Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03097 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03098 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0210 chi ∧
      Fin15AnchoredAtom0374 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0203 Fin15AnchoredAtom0210
    Fin15AnchoredAtom0374 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03099 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03100 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03101 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03102 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03103 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03104 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      ¬Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03105 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03106 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0211 chi ∧
      Fin15AnchoredAtom0375 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0204 Fin15AnchoredAtom0211
    Fin15AnchoredAtom0375 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03107 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03108 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03109 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03110 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03111 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03112 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      ¬Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03113 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03114 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0212 chi ∧
      Fin15AnchoredAtom0376 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0205 Fin15AnchoredAtom0212
    Fin15AnchoredAtom0376 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03115 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03116 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03117 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03118 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03119 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03120 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      ¬Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03121 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03122 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0213 chi ∧
      Fin15AnchoredAtom0377 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0206 Fin15AnchoredAtom0213
    Fin15AnchoredAtom0377 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03123 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03124 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03125 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03126 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03127 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03128 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      ¬Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03129 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03130 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0200 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0214 chi ∧
      Fin15AnchoredAtom0378 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0200 Fin15AnchoredAtom0207 Fin15AnchoredAtom0214
    Fin15AnchoredAtom0378 at hbad
  cases hcolor0 : chi ⟨2, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03131 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03132 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03133 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03134 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03135 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03136 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      ¬Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03137 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0215 chi ∧
      Fin15AnchoredAtom0379 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0202 Fin15AnchoredAtom0215
    Fin15AnchoredAtom0379 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03138 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03139 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03140 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03141 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03142 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03143 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03144 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0203 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03145 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0205 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03146 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0205 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03147 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0205 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03148 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0205 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03149 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0205 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03150 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0206 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03151 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0201 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0206 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03152 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0201 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0201 Fin15AnchoredAtom0206 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨2, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03153 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03154 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03155 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03156 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03157 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03158 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03159 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03160 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0203 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03161 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03162 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03163 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03164 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03165 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03166 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03167 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03168 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0204 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03169 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03170 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03171 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03172 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03173 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03174 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03175 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0205 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03176 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0205 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0205 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03177 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03178 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03179 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03180 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03181 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03182 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03183 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0206 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03184 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0206 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0206 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03185 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03186 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03187 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03188 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03189 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03190 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03191 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      ¬Fin15AnchoredAtom0207 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03192 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0202 chi ∧
      Fin15AnchoredAtom0207 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0202 Fin15AnchoredAtom0207 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨2, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03193 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
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

theorem fin15Anchored_clause03194 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
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

theorem fin15Anchored_clause03195 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
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

theorem fin15Anchored_clause03196 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0203 chi ∧
      Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
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

theorem fin15Anchored_clause03197 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
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

theorem fin15Anchored_clause03198 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
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

theorem fin15Anchored_clause03199 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0203 chi ∧
      ¬Fin15AnchoredAtom0204 chi ∧
      Fin15AnchoredAtom0226 chi ∧
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

end ErdosSzekeres

end
