module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 016. -/

theorem predecessorHalfFin13_clause05110 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05111 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05112 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0057 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0499 at hbad
  cases hcolor0 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05137 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05138 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05139 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05140 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05141 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05142 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05143 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05144 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05145 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0501 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05146 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0501 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05148 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0501 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05152 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0501 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05153 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0501 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05156 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0501 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05157 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0501 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05159 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0501 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05160 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0058 PredecessorHalfFin13Atom0060 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0501 at hbad
  cases hcolor0 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05209 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05210 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05211 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05212 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05213 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05214 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05215 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05216 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05217 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05218 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05219 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05220 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05224 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05225 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05228 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05229 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05231 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause05232 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0061 PredecessorHalfFin13Atom0063 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0504 at hbad
  cases hcolor0 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09241 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09242 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09243 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09244 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09245 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09246 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09247 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09248 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 5)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09249 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09250 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09252 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09254 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09256 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09257 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09258 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09260 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09261 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      ¬PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09263 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      ¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09264 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0123 chi ∧
      PredecessorHalfFin13Atom0131 chi ∧
      PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0672 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0123 PredecessorHalfFin13Atom0131
    PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0672 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 5, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 5, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09265 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09266 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09267 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09268 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09269 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09270 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09271 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09272 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09273 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0673 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09274 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0673 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09276 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0673 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09280 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0673 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09281 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0673 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09283 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0673 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09285 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      ¬PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0673 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09287 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0673 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09288 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0124 chi ∧
      PredecessorHalfFin13Atom0132 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0673 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0124 PredecessorHalfFin13Atom0132
    PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0673 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09289 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09290 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09291 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09292 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09293 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09294 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09295 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09296 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09297 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09298 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09299 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09300 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09304 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09305 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09306 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09309 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09310 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      ¬PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09311 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09312 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0125 chi ∧
      PredecessorHalfFin13Atom0133 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0674 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0125 PredecessorHalfFin13Atom0133
    PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0674 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09313 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09314 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09315 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09316 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09317 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09318 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09319 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09320 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09321 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0675 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09322 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0675 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09324 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0675 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09328 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0675 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09329 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0675 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09333 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0675 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09334 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      ¬PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0675 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09335 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0675 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09336 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0126 chi ∧
      PredecessorHalfFin13Atom0134 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0675 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0126 PredecessorHalfFin13Atom0134
    PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0675 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09337 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09338 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09339 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09340 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09341 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09342 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09343 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09344 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09345 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0676 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09346 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0676 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09348 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0676 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09352 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0676 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09353 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0676 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09354 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0676 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09357 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      ¬PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0676 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09359 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0676 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09360 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0122 chi ∧
      PredecessorHalfFin13Atom0127 chi ∧
      PredecessorHalfFin13Atom0135 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0676 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0127 PredecessorHalfFin13Atom0135
    PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0676 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause09361 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0122 chi ∧
      ¬PredecessorHalfFin13Atom0128 chi ∧
      PredecessorHalfFin13Atom0136 chi ∧
      ¬PredecessorHalfFin13Atom0172 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 3) (k := 4) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0122 PredecessorHalfFin13Atom0128 PredecessorHalfFin13Atom0136
    PredecessorHalfFin13Atom0172 at hbad
  cases hcolor0 : chi ⟨2, 3, 4, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 3, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
