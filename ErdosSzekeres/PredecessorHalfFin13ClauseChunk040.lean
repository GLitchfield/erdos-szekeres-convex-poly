module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 040. -/

theorem predecessorHalfFin13_clause13443 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
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

theorem predecessorHalfFin13_clause13444 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
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

theorem predecessorHalfFin13_clause13445 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
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

theorem predecessorHalfFin13_clause13446 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
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

theorem predecessorHalfFin13_clause13447 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
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

theorem predecessorHalfFin13_clause13448 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi) := by
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

theorem predecessorHalfFin13_clause13449 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13450 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13452 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13453 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13454 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13456 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13457 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13458 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13461 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13463 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      ¬PredecessorHalfFin13Atom0258 chi ∧
      PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13464 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0194 chi ∧
      PredecessorHalfFin13Atom0258 chi ∧
      ¬PredecessorHalfFin13Atom0847 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0194
    PredecessorHalfFin13Atom0258 PredecessorHalfFin13Atom0847 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13465 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13466 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13467 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13468 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13469 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13470 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13471 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13472 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0259 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13474 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0848 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13476 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0848 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13480 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0848 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0848 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13482 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0848 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13485 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0848 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13487 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      ¬PredecessorHalfFin13Atom0259 chi ∧
      PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0848 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13488 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0195 chi ∧
      PredecessorHalfFin13Atom0259 chi ∧
      ¬PredecessorHalfFin13Atom0848 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0195
    PredecessorHalfFin13Atom0259 PredecessorHalfFin13Atom0848 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13489 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13490 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13491 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13492 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13493 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13494 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13495 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13496 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13497 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13498 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13500 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13502 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13503 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13504 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13505 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13506 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13509 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13510 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13511 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      ¬PredecessorHalfFin13Atom0260 chi ∧
      PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13512 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0183 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0196 chi ∧
      PredecessorHalfFin13Atom0260 chi ∧
      ¬PredecessorHalfFin13Atom0849 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0183 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0196
    PredecessorHalfFin13Atom0260 PredecessorHalfFin13Atom0849 at hbad
  cases hcolor0 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13513 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13514 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13515 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13516 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13517 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13518 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13519 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13520 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0261 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13521 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0850 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13522 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0850 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13524 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0850 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13526 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0850 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13528 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0850 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13529 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0850 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13533 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0850 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13535 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      ¬PredecessorHalfFin13Atom0261 chi ∧
      PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0850 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13536 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0197 chi ∧
      PredecessorHalfFin13Atom0261 chi ∧
      ¬PredecessorHalfFin13Atom0850 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0197
    PredecessorHalfFin13Atom0261 PredecessorHalfFin13Atom0850 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13537 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13538 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13539 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13540 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13541 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13542 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13543 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13544 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0262 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13545 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0851 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13546 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0851 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13548 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0851 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13552 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0851 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13553 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0851 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13554 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0851 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13557 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0851 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13559 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      ¬PredecessorHalfFin13Atom0262 chi ∧
      PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0851 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13560 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0198 chi ∧
      PredecessorHalfFin13Atom0262 chi ∧
      ¬PredecessorHalfFin13Atom0851 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0198
    PredecessorHalfFin13Atom0262 PredecessorHalfFin13Atom0851 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13561 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13562 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13563 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13564 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13565 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13566 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13567 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13568 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0263 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13569 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0852 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13570 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0852 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13572 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0852 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13573 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0852 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13576 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0852 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13577 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0852 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13581 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0852 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13583 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      ¬PredecessorHalfFin13Atom0263 chi ∧
      PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0852 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13584 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0184 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0199 chi ∧
      PredecessorHalfFin13Atom0263 chi ∧
      ¬PredecessorHalfFin13Atom0852 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0184 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0199
    PredecessorHalfFin13Atom0263 PredecessorHalfFin13Atom0852 at hbad
  cases hcolor0 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13585 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13586 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13587 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13588 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13589 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13590 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13591 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13592 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0264 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13593 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0853 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13594 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0853 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13596 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0853 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13600 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0853 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13601 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0853 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13605 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      ¬PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0853 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13607 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      ¬PredecessorHalfFin13Atom0264 chi ∧
      PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0853 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13608 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0186 chi ∧
      PredecessorHalfFin13Atom0200 chi ∧
      PredecessorHalfFin13Atom0264 chi ∧
      ¬PredecessorHalfFin13Atom0853 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0186 PredecessorHalfFin13Atom0200
    PredecessorHalfFin13Atom0264 PredecessorHalfFin13Atom0853 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13609 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13610 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13611 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13612 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13613 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13614 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      ¬PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13615 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0185 chi ∧
      ¬PredecessorHalfFin13Atom0187 chi ∧
      PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause13616 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0185 chi ∧
      PredecessorHalfFin13Atom0187 chi ∧
      ¬PredecessorHalfFin13Atom0201 chi ∧
      PredecessorHalfFin13Atom0265 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0185 PredecessorHalfFin13Atom0187 PredecessorHalfFin13Atom0201
    PredecessorHalfFin13Atom0265 at hbad
  cases hcolor0 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
