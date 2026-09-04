module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 045. -/

theorem fin15Anchored_clause05760 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      ¬Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05761 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05762 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0352 chi ∧
      Fin15AnchoredAtom0380 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0339 Fin15AnchoredAtom0352
    Fin15AnchoredAtom0380 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05763 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05764 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05765 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05766 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05767 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05768 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      ¬Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05769 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05770 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0354 chi ∧
      Fin15AnchoredAtom0382 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0341 Fin15AnchoredAtom0354
    Fin15AnchoredAtom0382 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05771 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05772 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05773 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05774 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05775 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05776 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      ¬Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05777 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05778 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0355 chi ∧
      Fin15AnchoredAtom0383 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0342 Fin15AnchoredAtom0355
    Fin15AnchoredAtom0383 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05779 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05780 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05781 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05782 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05783 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05784 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      ¬Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05785 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05786 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0337 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0356 chi ∧
      Fin15AnchoredAtom0384 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 8) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0337 Fin15AnchoredAtom0343 Fin15AnchoredAtom0356
    Fin15AnchoredAtom0384 at hbad
  cases hcolor0 : chi ⟨5, 6, 8, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 8, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 8, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05787 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05788 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05789 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05790 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05791 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05792 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      ¬Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05793 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05794 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0357 chi ∧
      Fin15AnchoredAtom0385 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 10)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0339 Fin15AnchoredAtom0357
    Fin15AnchoredAtom0385 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 10, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 10, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05795 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05796 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05797 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05798 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      ¬Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05799 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05800 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05801 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0358 chi ∧
      Fin15AnchoredAtom0386 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0340 Fin15AnchoredAtom0358
    Fin15AnchoredAtom0386 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05802 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05803 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05804 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05805 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05806 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05807 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      ¬Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05808 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05809 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0359 chi ∧
      Fin15AnchoredAtom0387 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0341 Fin15AnchoredAtom0359
    Fin15AnchoredAtom0387 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05810 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05811 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05812 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05813 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05814 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05815 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      ¬Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05816 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05817 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0360 chi ∧
      Fin15AnchoredAtom0388 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0342 Fin15AnchoredAtom0360
    Fin15AnchoredAtom0388 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05818 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05819 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05820 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05821 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05822 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05823 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      ¬Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05824 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05825 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0338 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0361 chi ∧
      Fin15AnchoredAtom0389 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 9) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0338 Fin15AnchoredAtom0343 Fin15AnchoredAtom0361
    Fin15AnchoredAtom0389 at hbad
  cases hcolor0 : chi ⟨5, 6, 9, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 9, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 9, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05826 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05827 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05828 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05829 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05830 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05831 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      ¬Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05832 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05833 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0362 chi ∧
      Fin15AnchoredAtom0390 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 11)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0340 Fin15AnchoredAtom0362
    Fin15AnchoredAtom0390 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 11, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 11, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05834 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05835 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05836 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05837 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05838 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05839 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      ¬Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05840 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05841 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0363 chi ∧
      Fin15AnchoredAtom0391 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0341 Fin15AnchoredAtom0363
    Fin15AnchoredAtom0391 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05842 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05843 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05844 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05845 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05846 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05847 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      ¬Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05848 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05849 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0364 chi ∧
      Fin15AnchoredAtom0392 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0342 Fin15AnchoredAtom0364
    Fin15AnchoredAtom0392 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05850 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05851 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05852 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05853 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05854 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05855 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      ¬Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05856 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05857 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0339 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0365 chi ∧
      Fin15AnchoredAtom0393 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 10) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0339 Fin15AnchoredAtom0343 Fin15AnchoredAtom0365
    Fin15AnchoredAtom0393 at hbad
  cases hcolor0 : chi ⟨5, 6, 10, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 10, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 10, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05858 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05859 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05860 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05861 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      ¬Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05862 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05863 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05864 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0366 chi ∧
      Fin15AnchoredAtom0394 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 12)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0341 Fin15AnchoredAtom0366
    Fin15AnchoredAtom0394 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 12, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 12, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05865 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05866 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05867 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05868 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05869 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05870 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      ¬Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05871 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05872 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0367 chi ∧
      Fin15AnchoredAtom0395 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0342 Fin15AnchoredAtom0367
    Fin15AnchoredAtom0395 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05873 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0343 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05874 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0343 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05875 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0340 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0368 chi ∧
      ¬Fin15AnchoredAtom0396 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 11) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0340 Fin15AnchoredAtom0343 Fin15AnchoredAtom0368
    Fin15AnchoredAtom0396 at hbad
  cases hcolor0 : chi ⟨5, 6, 11, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 11, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 11, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05876 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05877 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05878 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05879 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05880 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05881 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      ¬Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05882 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0342 chi ∧
      Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05883 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0342 chi ∧
      ¬Fin15AnchoredAtom0369 chi ∧
      Fin15AnchoredAtom0397 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 13)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0342 Fin15AnchoredAtom0369
    Fin15AnchoredAtom0397 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 13, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 13, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 13, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05884 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0341 chi ∧
      ¬Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05885 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05886 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      ¬Fin15AnchoredAtom0370 chi ∧
      Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

theorem fin15Anchored_clause05887 (chi : TripleColoring 15)
    (hone : OneChangeOn chi Finset.univ) :
    ¬(¬Fin15AnchoredAtom0341 chi ∧
      Fin15AnchoredAtom0343 chi ∧
      Fin15AnchoredAtom0370 chi ∧
      ¬Fin15AnchoredAtom0398 chi) := by
  intro hbad
  have hallowed := hone (i := 5) (j := 6) (k := 12) (l := 14)
    (by decide) (by decide) (by decide)
    (by simp) (by simp) (by simp) (by simp)
  unfold Fin15AnchoredAtom0341 Fin15AnchoredAtom0343 Fin15AnchoredAtom0370
    Fin15AnchoredAtom0398 at hbad
  cases hcolor0 : chi ⟨5, 6, 12, by decide, by decide⟩ <;>
    cases hcolor1 : chi ⟨5, 6, 14, by decide, by decide⟩ <;>
      cases hcolor2 : chi ⟨5, 12, 14, by decide, by decide⟩ <;>
        cases hcolor3 : chi ⟨6, 12, 14, by decide, by decide⟩ <;>
          simp_all [TurnSequenceAllowed, Fin15AnchoredStrongQuad]

end ErdosSzekeres

end
