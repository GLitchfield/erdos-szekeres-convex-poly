module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 057. -/

theorem predecessorHalfFin13_clause16466 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16467 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16468 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16469 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16470 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16471 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16472 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16473 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16474 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16476 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16477 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16478 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16480 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16482 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16484 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16485 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16487 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16488 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0973 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0973 at hbad
  cases hcolor0 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16489 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16490 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16491 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16492 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16493 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16494 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16495 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16496 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16497 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0974 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16498 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0974 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16500 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0974 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16504 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0974 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16505 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0974 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16506 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0974 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16509 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0974 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16511 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0974 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16512 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0974 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0974 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16513 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16514 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16515 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16516 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16517 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16518 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16519 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16520 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16521 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0975 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16522 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0975 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16524 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0975 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16528 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0975 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16529 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0975 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16533 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0975 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16535 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0975 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16536 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0265 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0975 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0265
    PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0975 at hbad
  cases hcolor0 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16537 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16538 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16539 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16540 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16541 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16542 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16543 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16544 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 7) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16545 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0976 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16546 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0976 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16548 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0976 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16552 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0976 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0255 chi ∧
      ¬PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0976 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      ¬PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0976 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16559 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0976 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16560 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0255 chi ∧
      PredecessorHalfFin13Atom0256 chi ∧
      PredecessorHalfFin13Atom0266 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0976 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0255 PredecessorHalfFin13Atom0256 PredecessorHalfFin13Atom0266
    PredecessorHalfFin13Atom0276 PredecessorHalfFin13Atom0976 at hbad
  cases hcolor0 : chi ⟨6, 7, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 7, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16561 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16562 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16563 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16564 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16565 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16566 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16567 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16568 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16569 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0977 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16570 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0977 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16572 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0977 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16573 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0977 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16576 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0977 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16577 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0977 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0977 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0977 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16584 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0977 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0261
    PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0977 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16585 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16586 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16587 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16588 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16589 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16590 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16591 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16592 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0278 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16593 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0978 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16594 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0978 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16596 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0978 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16600 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0978 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0978 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16605 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0978 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16607 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0978 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16608 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0978 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0262
    PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0978 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16609 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16610 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16611 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16612 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16613 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16614 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16615 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16616 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0279 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16617 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16618 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16620 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16621 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16624 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16625 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16627 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16629 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16631 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16632 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0257 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0979 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0257 PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0263
    PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0979 at hbad
  cases hcolor0 : chi ⟨6, 8, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16633 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16634 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16635 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16636 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16637 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16638 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16639 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16640 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0280 chi) := by
  intro hbad
  have hallowed := hone (i := 6) (j := 8) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0264
    PredecessorHalfFin13Atom0280 at hbad
  cases hcolor0 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16641 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
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

end ErdosSzekeres

end
