module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 049. -/

theorem predecessorHalfFin13_clause15033 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0913 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15034 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0913 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15036 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0913 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15040 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0913 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15041 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0913 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15045 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0913 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15047 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0268 chi ∧
      PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0913 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15048 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0268 chi ∧
      ¬PredecessorHalfFin13Atom0913 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0268 PredecessorHalfFin13Atom0913 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15049 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15050 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15051 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15052 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15053 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15054 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15055 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15056 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0269 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15057 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0914 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15058 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0914 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15060 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0914 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15064 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0914 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15065 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0914 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15069 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0914 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15071 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0269 chi ∧
      PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0914 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15072 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0269 chi ∧
      ¬PredecessorHalfFin13Atom0914 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0269 PredecessorHalfFin13Atom0914 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15073 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15074 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15075 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15076 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15077 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15078 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15079 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15080 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0270 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15081 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0915 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15082 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0915 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15084 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0915 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15085 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0915 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15088 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0915 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15089 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0915 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15093 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0915 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15095 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0270 chi ∧
      PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0915 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15096 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0216 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0270 chi ∧
      ¬PredecessorHalfFin13Atom0915 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0216 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0270 PredecessorHalfFin13Atom0915 at hbad
  cases hcolor0 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15097 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15098 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15099 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15100 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15101 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15102 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15103 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15104 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0271 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15105 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15106 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15108 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15109 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15112 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15113 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15114 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15117 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15119 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15120 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0916 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0916 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15121 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15122 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15123 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0272 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15124 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15125 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0272 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15126 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15127 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0272 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15128 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0272 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15129 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15130 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15132 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15133 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15136 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15137 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15140 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15141 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15143 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      ¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15144 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0226 chi ∧
      PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0917 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0226
    PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0917 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15145 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15146 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15147 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15148 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15149 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15150 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15151 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15152 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15153 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15154 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15156 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15160 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15161 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15162 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15164 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15165 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15167 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15168 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0227 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0918 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0217 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0227
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0918 at hbad
  cases hcolor0 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15169 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15170 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15171 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15172 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15173 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15174 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15175 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15176 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15177 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15178 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15180 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15182 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15184 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15185 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15186 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15187 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15188 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15189 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15191 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15192 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0228 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0919 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0219 PredecessorHalfFin13Atom0228
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0919 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15193 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15194 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15195 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15196 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15197 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15198 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15199 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15200 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15201 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0920 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15202 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0920 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15204 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0920 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15208 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0229 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0920 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause15209 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0229 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0920 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0218 PredecessorHalfFin13Atom0220 PredecessorHalfFin13Atom0229
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0920 at hbad
  cases hcolor0 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
