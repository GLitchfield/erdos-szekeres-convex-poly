module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 031. -/

theorem fin15Anchored_clause03968 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03969 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03970 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      ¬Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03971 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03972 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0255 chi ∧
      Fin15AnchoredAtom0336 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 7)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0247 Fin15AnchoredAtom0255
    Fin15AnchoredAtom0336 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 7, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 7, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03973 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03974 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03975 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03976 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03977 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03978 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      ¬Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03979 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03980 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0256 chi ∧
      Fin15AnchoredAtom0337 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0248 Fin15AnchoredAtom0256
    Fin15AnchoredAtom0337 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03981 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03982 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03983 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03984 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03985 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03986 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03987 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03988 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0338 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0249 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0338 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03989 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03990 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03991 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03992 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03993 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03994 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03995 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03996 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0339 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0250 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0339 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03997 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03998 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03999 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04000 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04001 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04002 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04003 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04004 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0340 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0251 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0340 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04005 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04006 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04007 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04008 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04009 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04010 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04011 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04012 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0341 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0252 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0341 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04013 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04014 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04015 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04016 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04017 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04018 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04019 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04020 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0342 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0253 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0342 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04021 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04022 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04023 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04024 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04025 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04026 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04027 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04028 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0246 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0343 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0246 Fin15AnchoredAtom0254 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0343 at hbad
  cases hcolor0 : chi ⟨3, 5, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04029 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04030 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04031 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04032 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04033 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04034 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04035 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04036 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0344 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0248 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0344 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04037 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04038 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04039 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04040 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04041 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04042 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04043 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04044 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0345 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0249 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0345 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04045 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04046 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04047 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04048 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04049 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04050 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04051 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04052 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0346 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0250 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0346 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04053 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04054 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04055 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04056 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04057 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04058 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04059 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0251 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04060 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0251 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0347 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0251 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0347 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04061 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04062 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04063 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04064 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04065 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04066 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04067 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0252 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04068 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0252 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0348 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0252 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0348 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04069 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04070 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04071 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04072 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04073 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04074 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04075 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0253 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04076 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0253 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0349 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0253 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0349 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04077 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04078 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04079 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04080 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04081 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04082 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04083 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      ¬Fin15AnchoredAtom0254 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04084 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0247 chi ∧
      Fin15AnchoredAtom0254 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0350 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0247 Fin15AnchoredAtom0254 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0350 at hbad
  cases hcolor0 : chi ⟨3, 5, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04085 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04086 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04087 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04088 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04089 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04090 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04091 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0249 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04092 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0249 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0351 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0249 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0351 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04093 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0248 chi ∧
      ¬Fin15AnchoredAtom0250 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04094 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause04095 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0248 chi ∧
      Fin15AnchoredAtom0250 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0352 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 5) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0248 Fin15AnchoredAtom0250 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0352 at hbad
  cases hcolor0 : chi ⟨3, 5, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 5, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
