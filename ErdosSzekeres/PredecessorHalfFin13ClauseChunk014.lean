module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 014. -/

theorem predecessorHalfFin13_clause04541 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04542 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04543 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04544 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04545 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04546 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04547 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04548 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04550 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04552 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04559 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04560 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0056 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0056
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0476 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04561 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04562 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04563 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04564 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04565 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04566 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04567 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04568 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04569 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0477 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04570 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0477 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04571 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0477 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04572 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0477 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04576 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0477 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04577 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0477 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0477 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0477 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04584 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0477 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04585 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04586 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04587 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04588 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04589 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04590 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04591 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04592 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04593 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04594 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04595 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04596 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04598 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04600 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04605 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04607 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04608 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0478 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04633 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04634 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04635 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04636 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04637 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04638 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04639 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04640 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04641 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04642 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04643 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04644 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04646 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04648 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04649 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04653 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04655 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04656 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0480 at hbad
  cases hcolor0 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04657 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04658 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04659 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04660 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04661 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04662 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04663 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04664 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04665 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0481 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04666 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0481 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04668 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0481 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04672 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0481 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04673 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0481 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04677 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0481 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04679 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0481 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04680 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0481 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04705 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04706 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04707 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04708 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04709 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04710 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04711 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04712 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04713 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04714 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04715 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04716 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04718 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04720 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04721 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04725 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04726 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04727 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04728 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0483 at hbad
  cases hcolor0 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04753 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04754 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04755 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04756 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04757 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04758 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04759 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04760 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04761 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04762 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04763 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04764 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04766 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04768 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04769 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04773 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04775 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04776 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0051 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0265 PredecessorHalfFin13Atom0485 at hbad
  cases hcolor0 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04801 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04802 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04803 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04804 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04805 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04806 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      ¬PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04807 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04808 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0057 chi ∧
      PredecessorHalfFin13Atom0267 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 7) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0052 PredecessorHalfFin13Atom0053 PredecessorHalfFin13Atom0057
    PredecessorHalfFin13Atom0267 at hbad
  cases hcolor0 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
