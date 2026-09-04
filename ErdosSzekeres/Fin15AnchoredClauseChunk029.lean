module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 029. -/

theorem fin15Anchored_clause03712 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03713 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      ¬Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03714 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03715 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0257 chi ∧
      Fin15AnchoredAtom0302 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0240 Fin15AnchoredAtom0257
    Fin15AnchoredAtom0302 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03716 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03717 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03718 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03719 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03720 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03721 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      ¬Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03722 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03723 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0258 chi ∧
      Fin15AnchoredAtom0303 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0241 Fin15AnchoredAtom0258
    Fin15AnchoredAtom0303 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03724 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0242 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03725 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0242 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03726 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0242 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03727 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0242 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03728 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      ¬Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0242 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03729 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0242 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03730 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0259 chi ∧
      Fin15AnchoredAtom0304 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0242 Fin15AnchoredAtom0259
    Fin15AnchoredAtom0304 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03731 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03732 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03733 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03734 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03735 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03736 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      ¬Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03737 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03738 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0260 chi ∧
      Fin15AnchoredAtom0305 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0243 Fin15AnchoredAtom0260
    Fin15AnchoredAtom0305 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03739 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03740 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03741 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03742 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03743 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03744 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      ¬Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03745 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03746 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0261 chi ∧
      Fin15AnchoredAtom0306 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0244 Fin15AnchoredAtom0261
    Fin15AnchoredAtom0306 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03747 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03748 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03749 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03750 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03751 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03752 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      ¬Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03753 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03754 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0237 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0262 chi ∧
      Fin15AnchoredAtom0307 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 6) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0237 Fin15AnchoredAtom0245 Fin15AnchoredAtom0262
    Fin15AnchoredAtom0307 at hbad
  cases hcolor0 : chi ⟨3, 4, 6, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 6, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 6, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03755 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03756 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03757 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03758 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03759 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03760 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      ¬Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03761 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03762 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0263 chi ∧
      Fin15AnchoredAtom0308 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 8)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0239 Fin15AnchoredAtom0263
    Fin15AnchoredAtom0308 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 8, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 8, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03763 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03764 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03765 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03766 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03767 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03768 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      ¬Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03769 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03770 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0264 chi ∧
      Fin15AnchoredAtom0309 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0240 Fin15AnchoredAtom0264
    Fin15AnchoredAtom0309 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03771 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03772 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03773 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03774 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03775 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03776 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      ¬Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03777 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03778 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0265 chi ∧
      Fin15AnchoredAtom0310 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0241 Fin15AnchoredAtom0265
    Fin15AnchoredAtom0310 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03779 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03780 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03781 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03782 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03783 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03784 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      ¬Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03785 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0242 chi ∧
      Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03786 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0242 chi ∧
      ¬Fin15AnchoredAtom0266 chi ∧
      Fin15AnchoredAtom0311 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0242 Fin15AnchoredAtom0266
    Fin15AnchoredAtom0311 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03787 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03788 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03789 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03790 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03791 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03792 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      ¬Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03793 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03794 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0267 chi ∧
      Fin15AnchoredAtom0312 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0243 Fin15AnchoredAtom0267
    Fin15AnchoredAtom0312 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03795 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03796 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03797 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03798 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03799 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03800 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      ¬Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03801 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03802 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0268 chi ∧
      Fin15AnchoredAtom0313 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0244 Fin15AnchoredAtom0268
    Fin15AnchoredAtom0313 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03803 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03804 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03805 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03806 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03807 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03808 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      ¬Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03809 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      ¬Fin15AnchoredAtom0245 chi ∧
      Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03810 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0238 chi ∧
      Fin15AnchoredAtom0245 chi ∧
      ¬Fin15AnchoredAtom0269 chi ∧
      Fin15AnchoredAtom0314 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 7) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0238 Fin15AnchoredAtom0245 Fin15AnchoredAtom0269
    Fin15AnchoredAtom0314 at hbad
  cases hcolor0 : chi ⟨3, 4, 7, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 7, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 7, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03811 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03812 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03813 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03814 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03815 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03816 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      ¬Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03817 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0240 chi ∧
      Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03818 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0240 chi ∧
      ¬Fin15AnchoredAtom0270 chi ∧
      Fin15AnchoredAtom0315 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 9)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0240 Fin15AnchoredAtom0270
    Fin15AnchoredAtom0315 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 9, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 9, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 9, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03819 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03820 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03821 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03822 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03823 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03824 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      ¬Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03825 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0241 chi ∧
      Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03826 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0241 chi ∧
      ¬Fin15AnchoredAtom0271 chi ∧
      Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0241 Fin15AnchoredAtom0271
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03827 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03828 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03829 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03830 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03831 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03832 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      ¬Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03833 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0243 chi ∧
      Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03834 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0243 chi ∧
      ¬Fin15AnchoredAtom0273 chi ∧
      Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0243 Fin15AnchoredAtom0273
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03835 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03836 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03837 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03838 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0239 chi ∧
      Fin15AnchoredAtom0244 chi ∧
      Fin15AnchoredAtom0274 chi ∧
      ¬Fin15AnchoredAtom0319 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause03839 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0239 chi ∧
      ¬Fin15AnchoredAtom0244 chi ∧
      ¬Fin15AnchoredAtom0274 chi ∧
      Fin15AnchoredAtom0319 chi) := by
  intro hbad
  have hallowed := hone (i := 3) (j := 4) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0239 Fin15AnchoredAtom0244 Fin15AnchoredAtom0274
    Fin15AnchoredAtom0319 at hbad
  cases hcolor0 : chi ⟨3, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨3, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨3, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
