module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 032. -/

theorem predecessorHalfFin13_clause12034 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12035 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12036 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12038 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12040 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12041 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12045 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12047 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12048 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0788 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0164
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0788 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12049 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12050 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12051 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12052 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12053 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12054 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12055 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12056 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12057 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12058 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12059 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12060 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12062 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12064 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12065 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0161 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12069 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12071 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12072 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0161 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0789 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0161 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0165
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0789 at hbad
  cases hcolor0 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12073 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12074 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12075 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12076 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12077 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12078 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12079 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12080 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12081 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0790 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12082 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0790 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12084 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0790 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12088 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0790 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12089 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0790 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12091 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0162 chi ∧
      ¬PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0790 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12093 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0790 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12095 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0790 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12096 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0162 chi ∧
      PredecessorHalfFin13Atom0163 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0790 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0162 PredecessorHalfFin13Atom0163 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0790 at hbad
  cases hcolor0 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12097 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12098 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12099 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12100 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12101 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12102 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12103 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12104 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12105 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0791 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12106 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0791 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12112 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0791 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12113 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0164 chi ∧
      ¬PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0791 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12117 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      ¬PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0791 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12119 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0791 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12120 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0164 chi ∧
      PredecessorHalfFin13Atom0165 chi ∧
      PredecessorHalfFin13Atom0166 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0791 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0164 PredecessorHalfFin13Atom0165 PredecessorHalfFin13Atom0166
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0791 at hbad
  cases hcolor0 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12121 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12122 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12123 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12124 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12125 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12126 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12127 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12128 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 6)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12129 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0792 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12130 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0792 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12132 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0792 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12135 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0792 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12136 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0792 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12137 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0792 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12141 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      ¬PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0792 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12143 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      ¬PredecessorHalfFin13Atom0203 chi ∧
      PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0792 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12144 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0168 chi ∧
      PredecessorHalfFin13Atom0175 chi ∧
      PredecessorHalfFin13Atom0203 chi ∧
      ¬PredecessorHalfFin13Atom0792 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0168 PredecessorHalfFin13Atom0175
    PredecessorHalfFin13Atom0203 PredecessorHalfFin13Atom0792 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 6, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12145 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12146 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12147 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12148 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12149 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12150 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12151 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12152 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12153 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12154 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12156 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12158 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12159 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12160 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12161 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12163 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12165 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      ¬PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12167 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      ¬PredecessorHalfFin13Atom0204 chi ∧
      PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12168 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0169 chi ∧
      PredecessorHalfFin13Atom0176 chi ∧
      PredecessorHalfFin13Atom0204 chi ∧
      ¬PredecessorHalfFin13Atom0793 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0169 PredecessorHalfFin13Atom0176
    PredecessorHalfFin13Atom0204 PredecessorHalfFin13Atom0793 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 7, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12169 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12170 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12171 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12172 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12173 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12174 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12175 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12176 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12177 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0794 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12178 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0794 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12180 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0794 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12182 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0794 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12184 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0794 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12185 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0794 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12189 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      ¬PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0794 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12191 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      ¬PredecessorHalfFin13Atom0205 chi ∧
      PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0794 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12192 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0170 chi ∧
      PredecessorHalfFin13Atom0177 chi ∧
      PredecessorHalfFin13Atom0205 chi ∧
      ¬PredecessorHalfFin13Atom0794 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0170 PredecessorHalfFin13Atom0177
    PredecessorHalfFin13Atom0205 PredecessorHalfFin13Atom0794 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 8, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12193 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12194 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12195 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12196 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12197 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12198 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12199 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12200 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 5) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12201 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0795 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12202 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0795 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12204 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0795 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12208 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0795 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12209 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      ¬PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0795 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12213 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      ¬PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0795 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12215 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      ¬PredecessorHalfFin13Atom0206 chi ∧
      PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0795 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause12216 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0167 chi ∧
      PredecessorHalfFin13Atom0171 chi ∧
      PredecessorHalfFin13Atom0178 chi ∧
      PredecessorHalfFin13Atom0206 chi ∧
      ¬PredecessorHalfFin13Atom0795 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0167 PredecessorHalfFin13Atom0171 PredecessorHalfFin13Atom0178
    PredecessorHalfFin13Atom0206 PredecessorHalfFin13Atom0795 at hbad
  cases hcolor0 : chi ⟨3, 4, 5, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 5, 9, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

end ErdosSzekeres

end
