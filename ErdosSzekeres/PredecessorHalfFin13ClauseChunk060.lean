module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 060. -/

theorem predecessorHalfFin13_clause16981 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16984 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16985 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16988 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16989 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16991 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16992 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0271 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0994 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0271 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0275
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0994 at hbad
  cases hcolor0 : chi ⟨7, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16993 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16994 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16995 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16996 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16997 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16998 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause16999 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17000 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17001 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0995 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17002 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0995 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17004 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0995 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17008 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0995 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17009 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0272 chi ∧
      ¬PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0995 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17013 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0995 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17015 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0272 chi ∧
      PredecessorHalfFin13Atom0273 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0995 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0272 PredecessorHalfFin13Atom0273 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0995 at hbad
  cases hcolor0 : chi ⟨7, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17017 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17018 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17019 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17020 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17021 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17022 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17023 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17024 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 7) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17025 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17026 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17028 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17030 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17031 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17032 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17033 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0274 chi ∧
      ¬PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17037 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      ¬PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17039 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17040 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0274 chi ∧
      PredecessorHalfFin13Atom0275 chi ∧
      PredecessorHalfFin13Atom0276 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom0996 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0274 PredecessorHalfFin13Atom0275 PredecessorHalfFin13Atom0276
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom0996 at hbad
  cases hcolor0 : chi ⟨7, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨7, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨7, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17041 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17042 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17043 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17044 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17045 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17046 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17047 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17048 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0283 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17049 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17050 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17052 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17054 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17055 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17056 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17057 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17061 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17063 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17064 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0997 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0280
    PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0997 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17065 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17066 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17067 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17068 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17069 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17070 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17071 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17072 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0284 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17073 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17074 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17075 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17076 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17080 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17081 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17083 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0277 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17085 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17087 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17088 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0277 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0998 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0277 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0281
    PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0998 at hbad
  cases hcolor0 : chi ⟨8, 9, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17089 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17090 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17091 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17092 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17093 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17094 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17095 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17096 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 9) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17097 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0999 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17098 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0999 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17100 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0999 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17104 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0999 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17105 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0999 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17106 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0278 chi ∧
      ¬PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0999 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17109 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0999 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17111 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0999 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17112 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0278 chi ∧
      PredecessorHalfFin13Atom0279 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0999 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0278 PredecessorHalfFin13Atom0279 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0285 PredecessorHalfFin13Atom0999 at hbad
  cases hcolor0 : chi ⟨8, 9, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 9, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17113 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17114 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17115 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17116 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17117 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17118 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17119 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17120 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 8) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17121 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1000 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17122 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1000 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17124 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1000 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17128 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1000 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17129 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0280 chi ∧
      ¬PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1000 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17133 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      ¬PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1000 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17135 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1000 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17136 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0280 chi ∧
      PredecessorHalfFin13Atom0281 chi ∧
      PredecessorHalfFin13Atom0282 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1000 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0280 PredecessorHalfFin13Atom0281 PredecessorHalfFin13Atom0282
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1000 at hbad
  cases hcolor0 : chi ⟨8, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨8, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨8, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17137 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17138 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17139 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17140 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17141 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17142 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17143 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17144 (chi : TripleColoring 13)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi) := by
  intro hbad
  have hallowed := hone (i := 9) (j := 10) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17145 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17146 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17148 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17149 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17152 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17153 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17156 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0283 chi ∧
      ¬PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17157 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      ¬PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17159 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      ¬PredecessorHalfFin13Atom0286 chi ∧
      PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause17160 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom0283 chi ∧
      PredecessorHalfFin13Atom0284 chi ∧
      PredecessorHalfFin13Atom0285 chi ∧
      PredecessorHalfFin13Atom0286 chi ∧
      ¬PredecessorHalfFin13Atom1001 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0283 PredecessorHalfFin13Atom0284 PredecessorHalfFin13Atom0285
    PredecessorHalfFin13Atom0286 PredecessorHalfFin13Atom1001 at hbad
  cases hcolor0 : chi ⟨9, 10, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨9, 10, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨9, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨10, 11, 12, by decide, by decide⟩ <;>
          simp_all [PredecessorHalfFin13StrongQuad]

theorem predecessorHalfFin13_clause18151 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1167 chi ∧
      ¬PredecessorHalfFin13Atom0342 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0342 PredecessorHalfFin13Atom1167 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0061
  ] at hbad
  tauto

end ErdosSzekeres

end
