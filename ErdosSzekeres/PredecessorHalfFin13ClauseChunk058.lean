module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 058. -/

theorem predecessorHalfFin13_clause16642 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16643 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16644 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16646 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16647 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16648 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16649 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16652 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16653 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16654 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16655 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16656 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0980 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0980 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16657 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16658 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16659 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16660 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16661 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16662 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16663 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16664 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0281 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16665 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0981 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16666 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0981 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16668 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0981 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16672 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0981 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16673 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0981 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16676 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0981 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16677 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0981 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16679 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0981 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16680 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0981 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0981 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16681 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16682 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16683 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16684 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16685 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16686 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16687 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16688 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0282 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16689 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0982 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16690 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0982 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16692 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0982 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16695 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0982 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16696 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0982 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16701 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0982 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16703 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0982 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16704 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0982 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0282 PredecessorHalfFin13Atom0982 at hbad
  cases hcolor0 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16705 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16706 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16707 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16708 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16709 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16710 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16711 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16712 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16713 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0983 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16714 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0983 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16716 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0983 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16720 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0983 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16721 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0983 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16725 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0983 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16727 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0983 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16728 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0983 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0983 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16729 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16730 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16731 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16732 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16733 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16734 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16735 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16736 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16737 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0984 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16738 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0984 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16740 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0984 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16743 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0984 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16744 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0984 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16745 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0984 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16749 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0984 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16751 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0984 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16752 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0984 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0984 at hbad
  cases hcolor0 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16753 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16754 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16755 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16756 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16757 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16758 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16759 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16760 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16761 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0985 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16762 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0985 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16764 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0985 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16768 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0985 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16769 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0985 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16772 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0985 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16773 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0985 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16775 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0985 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16776 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0985 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0985 at hbad
  cases hcolor0 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16777 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16778 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16779 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16780 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16781 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16782 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16783 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16784 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16785 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0986 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16786 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0986 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16788 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0986 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16792 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0986 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16793 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0986 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16797 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0986 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16799 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0986 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16800 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0986 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0986 at hbad
  cases hcolor0 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16801 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16802 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16803 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16804 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16805 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16806 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16807 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16808 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0267 PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0271
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16809 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
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

theorem predecessorHalfFin13_clause16810 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
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

theorem predecessorHalfFin13_clause16811 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
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

theorem predecessorHalfFin13_clause16812 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
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

theorem predecessorHalfFin13_clause16814 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
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

theorem predecessorHalfFin13_clause16815 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
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

theorem predecessorHalfFin13_clause16816 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0267 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
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

theorem predecessorHalfFin13_clause16817 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
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

theorem predecessorHalfFin13_clause16819 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0267 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
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

end ErdosSzekeres

end
