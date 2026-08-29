module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 052. -/

theorem predecessorHalfFin13_clause15569 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0935 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15573 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0935 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15575 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0935 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15576 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0240 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0935 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0240
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0935 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15577 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15578 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15579 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15580 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15581 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15582 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15583 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15584 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15585 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0936 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15586 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0936 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15588 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0936 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15592 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0936 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15593 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0936 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15597 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0936 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15599 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0936 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15600 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0231 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0241 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0231 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0241
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0936 at hbad
  cases hcolor0 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15601 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15602 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15603 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15604 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15605 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15606 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15607 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15608 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15609 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15610 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15612 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15614 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15616 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15617 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15619 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15621 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15623 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15624 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0242 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0242
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0937 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15625 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15626 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15627 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15628 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15629 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15630 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15631 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15632 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15633 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0938 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15634 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0938 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15636 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0938 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15640 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0938 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15641 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0938 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15645 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0938 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15647 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0938 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15648 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0243
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0938 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15649 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15650 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15651 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15652 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15653 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15654 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15655 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15656 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15658 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0939 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15662 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0939 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15664 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0939 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15665 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0939 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15669 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0939 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15671 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0939 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15672 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0244 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0939 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0244
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0939 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15673 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15674 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15675 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15676 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15677 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15678 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15679 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15680 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15681 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15682 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15684 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15686 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15688 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15689 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15691 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15693 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15694 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15695 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15696 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0232 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0232 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0245
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0940 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15697 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15698 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15699 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15700 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15701 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15702 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15703 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15704 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15705 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0941 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15706 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0941 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15708 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0941 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15712 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0941 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15713 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0941 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15717 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0941 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15719 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0941 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15720 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0234 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0234 PredecessorHalfFin13Atom0246
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0941 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15721 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15722 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15723 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15724 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15725 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15726 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15727 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15728 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15730 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0942 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15732 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0942 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15736 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0942 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15737 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0942 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15741 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      ¬PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0942 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15743 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0942 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15744 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0235 chi ∧
      PredecessorHalfFin13Atom0247 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0942 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0235 PredecessorHalfFin13Atom0247
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0942 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15745 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15746 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15747 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15748 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15749 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15750 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15751 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15752 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0233 chi ∧
      PredecessorHalfFin13Atom0236 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0233 PredecessorHalfFin13Atom0236 PredecessorHalfFin13Atom0248
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15753 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0233 chi ∧
      ¬PredecessorHalfFin13Atom0236 chi ∧
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

end ErdosSzekeres

end
