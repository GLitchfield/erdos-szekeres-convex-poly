module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 020. -/

theorem predecessorHalfFin13_clause09898 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0699 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09899 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0699 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09900 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0699 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09904 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0699 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09905 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0699 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09909 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0699 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09911 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0699 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09912 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0158 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0158
    PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0699 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09913 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09914 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09915 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09916 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09917 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09918 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09919 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09920 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0195 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09921 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0700 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09922 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0700 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09923 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0700 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09924 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0700 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09927 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0700 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09928 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0700 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09933 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0700 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09935 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0700 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09936 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0159 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0159
    PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0700 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09937 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09938 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09939 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09940 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09941 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09942 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09943 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09944 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0196 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09945 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0701 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09946 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0701 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09948 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0701 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09951 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0701 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09952 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0701 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09953 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0701 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09957 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0701 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09959 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0701 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09960 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0160 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0160
    PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0701 at hbad
  cases hcolor0 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09961 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09962 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09963 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09964 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09965 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09966 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09967 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09968 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0197 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09969 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0702 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09970 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0702 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09972 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0702 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09976 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0702 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09977 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0702 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09979 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0702 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09981 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0702 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09983 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0702 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09984 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0161
    PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0702 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09985 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09986 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09987 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09988 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09989 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09990 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09991 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09992 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0198 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09993 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0703 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09994 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0703 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09995 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0703 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09996 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0703 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10000 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0703 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10001 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0703 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10005 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0703 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10007 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0703 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10008 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0162
    PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0703 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10009 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10010 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10011 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10012 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10013 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10014 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10015 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10016 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0199 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10017 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0704 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10018 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0704 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10020 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0704 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10024 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0704 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10025 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0704 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10029 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0704 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10031 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0704 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10032 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0163
    PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0704 at hbad
  cases hcolor0 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10033 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10034 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10035 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10036 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10037 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10038 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10039 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10040 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0200 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10041 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0705 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10042 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0705 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10043 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0705 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10044 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0705 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10047 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0705 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10049 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0705 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10053 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0705 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10055 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0705 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10056 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0129 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0705 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10057 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10058 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10059 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10060 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10061 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10062 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10063 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10064 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0201 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10065 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10066 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10068 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10071 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10072 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10073 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10076 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0128 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10077 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10079 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10080 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0706 at hbad
  cases hcolor0 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause10081 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0129 chi ∧
      ¬PredecessorHalfFin13Atom0130 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0129 PredecessorHalfFin13Atom0130 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0202 at hbad
  cases hcolor0 : chi ⟨2, 3, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
