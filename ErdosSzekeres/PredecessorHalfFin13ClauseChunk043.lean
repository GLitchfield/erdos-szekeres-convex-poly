module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 043. -/

theorem predecessorHalfFin13_clause13975 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
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

theorem predecessorHalfFin13_clause13976 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0194 chi ∧
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

theorem predecessorHalfFin13_clause13977 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13978 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13980 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13981 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13982 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13984 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13985 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13986 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13987 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13989 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13990 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13991 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13992 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0869 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0869 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13993 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13994 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13995 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13996 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13997 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13998 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13999 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14000 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14001 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14002 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14004 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14007 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14008 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14009 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14013 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14014 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14015 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14016 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0870 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0194 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0870 at hbad
  cases hcolor0 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14017 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14018 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14019 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14020 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14021 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14022 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14023 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14024 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14025 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0871 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0871 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14026 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0871 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0871 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14033 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0871 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0871 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14034 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0871 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0871 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14037 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0871 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0871 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14040 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0871 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0195 PredecessorHalfFin13Atom0196 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0871 at hbad
  cases hcolor0 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14041 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14042 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14043 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14044 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14045 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14046 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14047 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14048 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14049 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14050 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14052 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14055 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14056 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14057 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14058 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14061 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14063 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14064 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0872 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0872 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14065 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14066 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14067 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14068 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14069 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14070 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14071 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14072 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14073 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14074 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14076 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14078 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14080 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14081 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14084 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14085 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14087 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14088 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0873 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0197 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0873 at hbad
  cases hcolor0 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14089 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14090 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14091 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14092 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14093 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14094 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14095 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14096 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14097 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0874 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14098 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0874 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14100 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0874 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14104 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0874 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14105 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0874 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14108 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0874 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14109 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0874 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14112 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0874 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0198 PredecessorHalfFin13Atom0199 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0874 at hbad
  cases hcolor0 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14113 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14114 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14115 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14116 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14117 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14118 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14119 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14120 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14121 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0875 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14122 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0875 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14124 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0875 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14128 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0875 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14129 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0875 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14132 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0875 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14133 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0875 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14135 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0875 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14136 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0875 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0200 PredecessorHalfFin13Atom0201 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0875 at hbad
  cases hcolor0 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14137 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14138 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14139 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14140 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14141 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14142 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14143 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14144 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14145 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0876 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14146 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0876 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14148 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0876 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14152 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0876 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0210
    PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0876 at hbad
  cases hcolor0 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
