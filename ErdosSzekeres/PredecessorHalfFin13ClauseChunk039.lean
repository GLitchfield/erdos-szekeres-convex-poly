module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 039. -/

theorem predecessorHalfFin13_clause13265 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0839 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13269 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0839 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13271 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0839 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13272 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0179 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0179 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0839 at hbad
  cases hcolor0 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13273 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13274 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13275 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13276 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13277 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13278 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13279 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13280 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13281 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 PredecessorHalfFin13Atom0840 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13282 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 PredecessorHalfFin13Atom0840 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13284 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 PredecessorHalfFin13Atom0840 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13287 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 PredecessorHalfFin13Atom0840 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13288 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 PredecessorHalfFin13Atom0840 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13289 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0180 chi ∧
      ¬PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 PredecessorHalfFin13Atom0840 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13293 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      ¬PredecessorHalfFin13Atom0202 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 PredecessorHalfFin13Atom0840 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13296 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0180 chi ∧
      PredecessorHalfFin13Atom0181 chi ∧
      PredecessorHalfFin13Atom0202 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0180 PredecessorHalfFin13Atom0181 PredecessorHalfFin13Atom0202
    PredecessorHalfFin13Atom0251 PredecessorHalfFin13Atom0840 at hbad
  cases hcolor0 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13297 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13298 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13299 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13300 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13301 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13302 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13303 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13304 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13305 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0841 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13306 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0841 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13308 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0841 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13309 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0841 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13312 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0841 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13313 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0841 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13317 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0841 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13319 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0841 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13320 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0188 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0188
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0841 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13321 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13322 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13323 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13324 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13325 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13326 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13327 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13328 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13329 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0842 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13330 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0842 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13332 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0842 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13336 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0842 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13337 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0842 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13339 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0842 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13341 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0842 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13343 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0842 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13344 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0189 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0189
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0842 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13345 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13346 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13347 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13348 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13349 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13350 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13351 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13352 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13353 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13354 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13356 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13357 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13359 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13360 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13361 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13362 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13365 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13367 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13368 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0190 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0190
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0843 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13369 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13370 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13371 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13372 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13373 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13374 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13375 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13376 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13377 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13378 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13380 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13381 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13382 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13383 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13384 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13385 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13389 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13391 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13392 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0191 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0191
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0844 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13393 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13394 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13395 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13396 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13397 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13398 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13399 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13400 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13401 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0845 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13402 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0845 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13404 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0845 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13406 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0845 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13408 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0845 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13409 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0845 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13413 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0845 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13415 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0845 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13416 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0182 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0192 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0182 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0192
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0845 at hbad
  cases hcolor0 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13417 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13418 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13419 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13420 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13421 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13422 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13423 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13424 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13425 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0846 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13426 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0846 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13428 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0846 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13432 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0846 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13433 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0846 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13434 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0846 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13437 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0846 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13439 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0846 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13440 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0193 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0193
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0846 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13441 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13442 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
