module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 047. -/

theorem predecessorHalfFin13_clause14687 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0217
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0898 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14688 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0217 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0898 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0217
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0898 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14689 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14690 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14691 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14692 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14693 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14694 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14695 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14696 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14697 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14698 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14699 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14700 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14701 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14702 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14704 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14705 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14707 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14709 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14711 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14712 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0218 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0899 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0218
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0899 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14713 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14714 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14715 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14716 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14717 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14718 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14719 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14720 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14721 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0900 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14722 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0900 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14724 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0900 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14728 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0900 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14729 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0900 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14733 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0900 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14735 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0900 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14736 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0219 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0900 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0219
    PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0900 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14737 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14738 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14739 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14740 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14741 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14742 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14743 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14744 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14745 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0901 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14746 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0901 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14748 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0901 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14750 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0901 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14752 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0901 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14753 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0901 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14757 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0901 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14759 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0901 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14760 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0210 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0220 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0901 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0210 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0220
    PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0901 at hbad
  cases hcolor0 : chi ⟨4, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14761 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14762 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14763 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14764 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14765 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14766 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14767 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14768 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14769 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0902 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14770 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0902 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14772 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0902 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14774 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0902 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14776 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0902 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14777 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0902 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14781 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0902 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14783 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      ¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0902 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14784 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0221 chi ∧
      PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0902 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0221
    PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0902 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14785 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14786 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14787 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14788 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14789 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14790 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14791 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14792 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14793 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0903 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14794 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0903 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14796 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0903 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14800 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0903 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14801 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0903 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14802 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0903 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14805 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0903 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14807 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0903 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14808 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0222 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0903 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0222
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0903 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14809 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14810 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14811 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14813 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14814 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14815 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14816 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14817 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14818 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14823 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14824 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14825 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14826 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14829 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14830 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      ¬PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14831 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14832 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0214 chi ∧
      PredecessorHalfFin13Atom0223 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0904 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0214 PredecessorHalfFin13Atom0223
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0904 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14833 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14834 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14835 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14836 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14837 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14838 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14839 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14840 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14841 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0905 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14842 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0905 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14844 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0905 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14847 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0905 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14848 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0905 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14849 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      ¬PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0905 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14853 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      ¬PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0905 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14855 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0905 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14856 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0211 chi ∧
      PredecessorHalfFin13Atom0215 chi ∧
      PredecessorHalfFin13Atom0224 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0905 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0211 PredecessorHalfFin13Atom0215 PredecessorHalfFin13Atom0224
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0905 at hbad
  cases hcolor0 : chi ⟨4, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14857 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14858 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14859 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14860 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0212 chi ∧
      PredecessorHalfFin13Atom0213 chi ∧
      PredecessorHalfFin13Atom0225 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause14861 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0212 chi ∧
      ¬PredecessorHalfFin13Atom0213 chi ∧
      ¬PredecessorHalfFin13Atom0225 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 4) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0212 PredecessorHalfFin13Atom0213 PredecessorHalfFin13Atom0225
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
