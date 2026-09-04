module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 021. -/

theorem fin15Anchored_clause02688 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02689 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02690 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02691 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02692 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      ¬Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02693 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02694 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0216 chi ∧
      Fin15AnchoredAtom0316 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0186 Fin15AnchoredAtom0216
    Fin15AnchoredAtom0316 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02695 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02696 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02697 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02698 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02699 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02700 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      ¬Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02701 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02702 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0218 chi ∧
      Fin15AnchoredAtom0318 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0188 Fin15AnchoredAtom0218
    Fin15AnchoredAtom0318 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02703 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      ¬Fin15AnchoredAtom0319 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0189 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0319 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02704 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0219 chi ∧
      Fin15AnchoredAtom0319 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0189 Fin15AnchoredAtom0219
    Fin15AnchoredAtom0319 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02705 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02706 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02707 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0320 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02708 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0184 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02709 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0320 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02710 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      ¬Fin15AnchoredAtom0320 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02711 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0184 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0220 chi ∧
      Fin15AnchoredAtom0320 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0184 Fin15AnchoredAtom0190 Fin15AnchoredAtom0220
    Fin15AnchoredAtom0320 at hbad
  cases hcolor0 : chi ⟨2, 4, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02712 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02713 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02714 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02715 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02716 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02717 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      ¬Fin15AnchoredAtom0321 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02718 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02719 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0221 chi ∧
      Fin15AnchoredAtom0321 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0186 Fin15AnchoredAtom0221
    Fin15AnchoredAtom0321 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02720 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02721 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02722 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02723 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02724 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02725 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      ¬Fin15AnchoredAtom0322 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02726 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02727 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0222 chi ∧
      Fin15AnchoredAtom0322 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0187 Fin15AnchoredAtom0222
    Fin15AnchoredAtom0322 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02728 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02729 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02730 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02731 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02732 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02733 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      ¬Fin15AnchoredAtom0323 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02734 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02735 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0223 chi ∧
      Fin15AnchoredAtom0323 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0188 Fin15AnchoredAtom0223
    Fin15AnchoredAtom0323 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02736 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02737 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02738 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02739 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02740 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02741 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      ¬Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02742 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02743 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0224 chi ∧
      Fin15AnchoredAtom0324 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0189 Fin15AnchoredAtom0224
    Fin15AnchoredAtom0324 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02744 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02745 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02746 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02747 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02748 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02749 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      ¬Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02750 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02751 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0185 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0225 chi ∧
      Fin15AnchoredAtom0325 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0185 Fin15AnchoredAtom0190 Fin15AnchoredAtom0225
    Fin15AnchoredAtom0325 at hbad
  cases hcolor0 : chi ⟨2, 4, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02752 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02753 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02754 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02755 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02756 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02757 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      ¬Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02758 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02759 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0226 chi ∧
      Fin15AnchoredAtom0326 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0187 Fin15AnchoredAtom0226
    Fin15AnchoredAtom0326 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02760 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02761 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02762 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02763 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02764 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02765 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      ¬Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02766 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02767 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0227 chi ∧
      Fin15AnchoredAtom0327 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0188 Fin15AnchoredAtom0227
    Fin15AnchoredAtom0327 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02768 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02769 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02770 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02771 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02772 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02773 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      ¬Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02774 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02775 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0228 chi ∧
      Fin15AnchoredAtom0328 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0189 Fin15AnchoredAtom0228
    Fin15AnchoredAtom0328 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02776 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02777 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02778 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02779 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02780 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02781 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      ¬Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02782 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02783 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0186 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0229 chi ∧
      Fin15AnchoredAtom0329 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0186 Fin15AnchoredAtom0190 Fin15AnchoredAtom0229
    Fin15AnchoredAtom0329 at hbad
  cases hcolor0 : chi ⟨2, 4, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02784 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02785 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02786 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02787 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02788 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02789 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0230 chi ∧
      ¬Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02790 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0230 chi ∧
      Fin15AnchoredAtom0330 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0188 Fin15AnchoredAtom0230
    Fin15AnchoredAtom0330 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02791 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0189 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02792 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0189 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02793 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0231 chi ∧
      ¬Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0189 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02794 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0187 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0189 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02795 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0187 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0231 chi ∧
      Fin15AnchoredAtom0331 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0187 Fin15AnchoredAtom0189 Fin15AnchoredAtom0231
    Fin15AnchoredAtom0331 at hbad
  cases hcolor0 : chi ⟨2, 4, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02796 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02797 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02798 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02799 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02800 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02801 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      ¬Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02802 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02803 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0233 chi ∧
      Fin15AnchoredAtom0333 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0189 Fin15AnchoredAtom0233
    Fin15AnchoredAtom0333 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02804 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02805 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02806 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02807 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02808 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02809 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      ¬Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02810 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0188 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02811 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0188 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0234 chi ∧
      Fin15AnchoredAtom0334 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0188 Fin15AnchoredAtom0190 Fin15AnchoredAtom0234
    Fin15AnchoredAtom0334 at hbad
  cases hcolor0 : chi ⟨2, 4, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02812 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0189 chi ∧
      ¬Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02813 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02814 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      ¬Fin15AnchoredAtom0235 chi ∧
      Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause02815 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0189 chi ∧
      Fin15AnchoredAtom0190 chi ∧
      Fin15AnchoredAtom0235 chi ∧
      ¬Fin15AnchoredAtom0335 chi) := by
  intro hbad
  have hallowed := hone (i := 2) (j := 4) (k := 13) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0189 Fin15AnchoredAtom0190 Fin15AnchoredAtom0235
    Fin15AnchoredAtom0335 at hbad
  cases hcolor0 : chi ⟨2, 4, 13, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨2, 4, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨2, 13, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨4, 13, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
