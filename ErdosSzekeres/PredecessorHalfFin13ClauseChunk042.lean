module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 042. -/

theorem predecessorHalfFin13_clause13791 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0861 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13792 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0861 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13793 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0861 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13797 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0861 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13799 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0861 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13800 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0861 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0861 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13801 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13802 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13803 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13804 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13805 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13806 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13807 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13808 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13809 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13810 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13812 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13814 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13816 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13817 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13818 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13821 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13823 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13824 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0862 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0189 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0862 at hbad
  cases hcolor0 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13825 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13826 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13827 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13828 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13829 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13830 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13831 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13832 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13833 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0863 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13834 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0863 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13836 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0863 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13838 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0863 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13840 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0863 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13841 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0863 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13845 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0863 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13847 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0863 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13848 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0863 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0863 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13849 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13850 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13851 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13852 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13853 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13854 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13855 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13856 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13857 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0864 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13858 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0864 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13860 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0864 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13864 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0864 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13865 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0864 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13869 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0864 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13871 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0864 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13872 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0864 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0190 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0864 at hbad
  cases hcolor0 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13873 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13874 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13875 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13876 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13877 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13878 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13879 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13880 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13881 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0865 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13882 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0865 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13888 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0865 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13889 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0865 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13893 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0865 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13895 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0865 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13896 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0865 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0191 PredecessorHalfFin13Atom0192 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0865 at hbad
  cases hcolor0 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13897 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13898 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13899 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13900 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13901 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13902 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13903 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13904 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13905 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0866 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13906 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0866 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13908 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0866 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13912 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0866 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13913 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0866 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13917 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0866 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13919 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0866 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13920 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0866 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0866 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13921 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13922 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13923 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13924 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13925 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13926 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13927 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13928 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13929 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13930 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13932 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13933 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13935 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13936 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13937 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13941 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13943 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13944 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0867 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0867 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13945 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13946 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13947 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13948 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13949 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13950 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13951 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13952 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13953 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0868 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13954 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0868 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13956 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0868 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13960 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0868 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13961 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0868 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13965 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0868 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13967 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0868 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13968 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0868 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0193 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0868 at hbad
  cases hcolor0 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13969 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13970 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13971 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13972 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13973 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13974 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
