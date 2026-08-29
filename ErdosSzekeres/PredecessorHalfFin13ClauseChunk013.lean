module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 013. -/

theorem predecessorHalfFin13_clause04247 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      ¬PredecessorHalfFin13Atom0243 chi ∧
      PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0463 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04248 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0058 chi ∧
      PredecessorHalfFin13Atom0243 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0058
    PredecessorHalfFin13Atom0243 PredecessorHalfFin13Atom0463 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04273 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04274 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04275 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04276 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04277 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04278 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04279 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04280 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04281 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04282 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04283 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04284 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04286 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04288 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04289 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04293 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04295 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      ¬PredecessorHalfFin13Atom0245 chi ∧
      PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04296 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0041 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0060 chi ∧
      PredecessorHalfFin13Atom0245 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0041 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0060
    PredecessorHalfFin13Atom0245 PredecessorHalfFin13Atom0465 at hbad
  cases hcolor0 : chi ⟨0, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04297 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04298 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04299 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04300 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04301 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04302 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04303 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04304 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04305 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0466 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04306 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0466 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04308 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0466 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04312 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0466 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04313 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0466 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04317 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0466 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04319 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      ¬PredecessorHalfFin13Atom0246 chi ∧
      PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0466 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04320 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0061 chi ∧
      PredecessorHalfFin13Atom0246 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0061
    PredecessorHalfFin13Atom0246 PredecessorHalfFin13Atom0466 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04345 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04346 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04347 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04348 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04349 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04350 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04351 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04352 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04353 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04354 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04355 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04356 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04360 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04361 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04364 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0042 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04365 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04367 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      ¬PredecessorHalfFin13Atom0248 chi ∧
      PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04368 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0042 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0063 chi ∧
      PredecessorHalfFin13Atom0248 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0042 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0063
    PredecessorHalfFin13Atom0248 PredecessorHalfFin13Atom0468 at hbad
  cases hcolor0 : chi ⟨0, 5, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04393 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04394 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04395 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04396 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04397 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04398 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04399 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04400 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 5) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04401 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0470 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04402 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0470 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04404 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0470 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04408 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0470 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04409 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0043 chi ∧
      ¬PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0470 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04413 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      ¬PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0470 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04415 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      ¬PredecessorHalfFin13Atom0250 chi ∧
      PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0470 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04416 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0043 chi ∧
      PredecessorHalfFin13Atom0045 chi ∧
      PredecessorHalfFin13Atom0065 chi ∧
      PredecessorHalfFin13Atom0250 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0043 PredecessorHalfFin13Atom0045 PredecessorHalfFin13Atom0065
    PredecessorHalfFin13Atom0250 PredecessorHalfFin13Atom0470 at hbad
  cases hcolor0 : chi ⟨0, 5, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04441 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04442 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04443 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04444 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04445 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04446 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04447 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04448 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04449 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04450 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04451 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04452 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04456 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04457 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04461 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04462 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      ¬PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04463 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      ¬PredecessorHalfFin13Atom0252 chi ∧
      PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04464 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0047 chi ∧
      PredecessorHalfFin13Atom0052 chi ∧
      PredecessorHalfFin13Atom0252 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0047 PredecessorHalfFin13Atom0052
    PredecessorHalfFin13Atom0252 PredecessorHalfFin13Atom0472 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04465 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04466 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04467 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04468 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04469 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04470 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04471 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04472 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04473 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04474 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04475 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04476 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04478 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04480 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04481 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04485 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      ¬PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04487 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      ¬PredecessorHalfFin13Atom0253 chi ∧
      PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04488 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0048 chi ∧
      PredecessorHalfFin13Atom0053 chi ∧
      PredecessorHalfFin13Atom0253 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0048 PredecessorHalfFin13Atom0053
    PredecessorHalfFin13Atom0253 PredecessorHalfFin13Atom0473 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04489 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04490 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04491 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04492 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04493 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04494 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04495 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04496 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi) := by
  intro hbad
  have hallowed := hone (i := 0) (j := 6) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04497 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04498 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04500 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04502 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04504 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04505 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04508 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      ¬PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04509 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      ¬PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04511 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      ¬PredecessorHalfFin13Atom0254 chi ∧
      PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04512 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0049 chi ∧
      PredecessorHalfFin13Atom0054 chi ∧
      PredecessorHalfFin13Atom0254 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0046 PredecessorHalfFin13Atom0049 PredecessorHalfFin13Atom0054
    PredecessorHalfFin13Atom0254 PredecessorHalfFin13Atom0474 at hbad
  cases hcolor0 : chi ⟨0, 6, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨0, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨0, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 7, 10, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause04537 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
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

theorem predecessorHalfFin13_clause04538 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
      ¬PredecessorHalfFin13Atom0056 chi ∧
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

theorem predecessorHalfFin13_clause04539 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
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

theorem predecessorHalfFin13_clause04540 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0046 chi ∧
      PredecessorHalfFin13Atom0051 chi ∧
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

end ErdosSzekeres

end
