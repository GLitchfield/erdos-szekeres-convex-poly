module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 059. -/

theorem predecessorHalfFin13_clause16821 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0987 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16822 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0987 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16823 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0987 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16824 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0987 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0987 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16825 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16826 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16827 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16828 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16829 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16830 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16831 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16832 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16833 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16834 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16835 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16836 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16837 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16838 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16839 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16840 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16841 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16842 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16843 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16845 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16846 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16847 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16848 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0988 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0272
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0988 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16849 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16850 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16851 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16852 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16853 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16854 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16855 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16856 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16857 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16858 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16860 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16862 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16864 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16865 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16866 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16868 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16869 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16870 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16871 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16872 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0989 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0273
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0989 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16873 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16874 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16875 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16876 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16877 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16878 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16879 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16880 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16881 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16882 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16884 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16885 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16886 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16887 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16888 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16889 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16893 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16895 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16896 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0990 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0990 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16897 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16898 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16899 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16900 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16901 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16902 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16903 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16904 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16905 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16906 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16908 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16912 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16913 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16914 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16916 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16917 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16919 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16920 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0991 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0991 at hbad
  cases hcolor0 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16921 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16922 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16923 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16924 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16925 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16926 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16927 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16928 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16929 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0992 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16930 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0992 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16932 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0992 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16933 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0992 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16936 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0992 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16941 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0992 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16943 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0992 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16944 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0992 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0992 at hbad
  cases hcolor0 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16945 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16946 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16947 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16948 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16949 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16950 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16951 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16952 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16953 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0993 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16954 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0993 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16956 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0993 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16960 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0993 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16961 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0993 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16963 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0993 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16965 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0993 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16967 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0993 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16968 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0993 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0274
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0993 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16969 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16970 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16971 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16972 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16973 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16974 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16975 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16976 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16977 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16978 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16980 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
