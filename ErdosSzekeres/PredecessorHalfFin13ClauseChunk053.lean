module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 053. -/

theorem predecessorHalfFin13_clause15754 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0943 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15756 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0943 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15760 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0943 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15761 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0943 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15765 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0943 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15766 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0943 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15767 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0943 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15768 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0943 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15769 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15770 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15771 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15772 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15773 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15774 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15775 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15776 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15777 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0944 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15778 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0944 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15780 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0944 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15784 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0944 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15785 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0944 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15787 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0944 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15789 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0944 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15791 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0944 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15792 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0249 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0944 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0249
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0944 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15793 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15794 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15795 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15796 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15797 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15798 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15799 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15800 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15801 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15802 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15803 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15804 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15807 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15808 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15809 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15813 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15814 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15815 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15816 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0250
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0945 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15817 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15818 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15819 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15820 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15821 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15822 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15823 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15824 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15826 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0946 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 PredecessorHalfFin13Atom0946 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15833 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0946 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 PredecessorHalfFin13Atom0946 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15837 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 PredecessorHalfFin13Atom0946 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15839 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0946 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 PredecessorHalfFin13Atom0946 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15840 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0251 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0946 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0251
    PredecessorHalfFin13Atom0266 PredecessorHalfFin13Atom0946 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15841 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15842 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15843 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15844 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15845 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15846 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15847 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15848 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15849 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15850 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15852 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15855 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15856 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15857 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15859 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15861 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15863 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15864 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0238 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0238 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0947 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15865 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15866 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15867 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15868 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15869 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15870 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15871 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15872 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15873 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15874 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15876 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15877 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15878 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15879 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15880 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15881 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15882 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15885 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15887 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15888 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0239 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0239 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0948 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15889 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15890 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15891 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15892 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15893 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15894 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15895 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15896 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15897 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0949 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15898 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0949 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15900 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0949 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15902 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0949 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15904 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0949 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15905 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0949 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15909 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0949 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15911 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0949 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15912 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0949 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0240 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0949 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15913 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15914 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15915 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15916 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15917 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15918 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15919 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15920 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15921 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0950 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15922 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0950 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15924 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0950 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15928 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0950 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15929 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0950 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15933 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0950 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15935 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0950 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15936 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0237 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0237 PredecessorHalfFin13Atom0241 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0950 at hbad
  cases hcolor0 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
