module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 151. -/

theorem fin15Anchored_clause19328 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2612 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom0701 Fin15AnchoredAtom0708
    Fin15AnchoredAtom0736 Fin15AnchoredAtom1611 Fin15AnchoredAtom2612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00481
  ] at hbad
  tauto

theorem fin15Anchored_clause19329 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00737
  ] at hbad
  tauto

theorem fin15Anchored_clause19330 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00737
  ] at hbad
  tauto

theorem fin15Anchored_clause19331 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom2613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00737
  ] at hbad
  tauto

theorem fin15Anchored_clause19332 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00737
  ] at hbad
  tauto

theorem fin15Anchored_clause19333 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2613 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom2613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00737
  ] at hbad
  tauto

theorem fin15Anchored_clause19334 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2613 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom0702 Fin15AnchoredAtom0709
    Fin15AnchoredAtom0737 Fin15AnchoredAtom1612 Fin15AnchoredAtom2613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00737
  ] at hbad
  tauto

theorem fin15Anchored_clause19335 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2614 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01249
  ] at hbad
  tauto

theorem fin15Anchored_clause19336 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2614 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01249
  ] at hbad
  tauto

theorem fin15Anchored_clause19337 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2614 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01249
  ] at hbad
  tauto

theorem fin15Anchored_clause19338 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2614 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01249
  ] at hbad
  tauto

theorem fin15Anchored_clause19339 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2614 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom2614 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01249
  ] at hbad
  tauto

theorem fin15Anchored_clause19340 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2614 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom0703 Fin15AnchoredAtom0710
    Fin15AnchoredAtom0738 Fin15AnchoredAtom1613 Fin15AnchoredAtom2614 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01249
  ] at hbad
  tauto

theorem fin15Anchored_clause19341 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02273
  ] at hbad
  tauto

theorem fin15Anchored_clause19342 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom0704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0704 Fin15AnchoredAtom2615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02273
  ] at hbad
  tauto

theorem fin15Anchored_clause19343 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom2615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02273
  ] at hbad
  tauto

theorem fin15Anchored_clause19344 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2615 chi ∧
      ¬Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1614 Fin15AnchoredAtom2615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02273
  ] at hbad
  tauto

theorem fin15Anchored_clause19345 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2615 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom0704 Fin15AnchoredAtom0711
    Fin15AnchoredAtom0739 Fin15AnchoredAtom1614 Fin15AnchoredAtom2615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02273
  ] at hbad
  tauto

theorem fin15Anchored_clause19346 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04321
  ] at hbad
  tauto

theorem fin15Anchored_clause19347 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04321
  ] at hbad
  tauto

theorem fin15Anchored_clause19348 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04321
  ] at hbad
  tauto

theorem fin15Anchored_clause19349 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04321
  ] at hbad
  tauto

theorem fin15Anchored_clause19350 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2616 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom2616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04321
  ] at hbad
  tauto

theorem fin15Anchored_clause19351 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2616 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom0705 Fin15AnchoredAtom0712
    Fin15AnchoredAtom0740 Fin15AnchoredAtom1615 Fin15AnchoredAtom2616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04321
  ] at hbad
  tauto

theorem fin15Anchored_clause19352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08417
  ] at hbad
  tauto

theorem fin15Anchored_clause19353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom2617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08417
  ] at hbad
  tauto

theorem fin15Anchored_clause19354 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08417
  ] at hbad
  tauto

theorem fin15Anchored_clause19355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08417
  ] at hbad
  tauto

theorem fin15Anchored_clause19356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2617 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom2617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08417
  ] at hbad
  tauto

theorem fin15Anchored_clause19357 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2617 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom0706 Fin15AnchoredAtom0713
    Fin15AnchoredAtom0741 Fin15AnchoredAtom1616 Fin15AnchoredAtom2617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08417
  ] at hbad
  tauto

theorem fin15Anchored_clause19358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16609
  ] at hbad
  tauto

theorem fin15Anchored_clause19359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16609
  ] at hbad
  tauto

theorem fin15Anchored_clause19360 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16609
  ] at hbad
  tauto

theorem fin15Anchored_clause19361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16609
  ] at hbad
  tauto

theorem fin15Anchored_clause19362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2618 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom2618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16609
  ] at hbad
  tauto

theorem fin15Anchored_clause19363 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2618 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom0707 Fin15AnchoredAtom0714
    Fin15AnchoredAtom0742 Fin15AnchoredAtom1617 Fin15AnchoredAtom2618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16609
  ] at hbad
  tauto

theorem fin15Anchored_clause19364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom2619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00865
  ] at hbad
  tauto

theorem fin15Anchored_clause19365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00865
  ] at hbad
  tauto

theorem fin15Anchored_clause19366 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00865
  ] at hbad
  tauto

theorem fin15Anchored_clause19367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom2619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00865
  ] at hbad
  tauto

theorem fin15Anchored_clause19368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2619 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom2619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00865
  ] at hbad
  tauto

theorem fin15Anchored_clause19369 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2619 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom0702 Fin15AnchoredAtom0715
    Fin15AnchoredAtom0743 Fin15AnchoredAtom1618 Fin15AnchoredAtom2619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00865
  ] at hbad
  tauto

theorem fin15Anchored_clause19370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom2620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01377
  ] at hbad
  tauto

theorem fin15Anchored_clause19371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01377
  ] at hbad
  tauto

theorem fin15Anchored_clause19372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2620 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom2620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01377
  ] at hbad
  tauto

theorem fin15Anchored_clause19373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2620 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom0703 Fin15AnchoredAtom0716
    Fin15AnchoredAtom0744 Fin15AnchoredAtom1619 Fin15AnchoredAtom2620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01377
  ] at hbad
  tauto

theorem fin15Anchored_clause19374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom2622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04449
  ] at hbad
  tauto

theorem fin15Anchored_clause19375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04449
  ] at hbad
  tauto

theorem fin15Anchored_clause19376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom2622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04449
  ] at hbad
  tauto

theorem fin15Anchored_clause19377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2622 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom2622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04449
  ] at hbad
  tauto

theorem fin15Anchored_clause19378 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2622 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom0705 Fin15AnchoredAtom0718
    Fin15AnchoredAtom0746 Fin15AnchoredAtom1621 Fin15AnchoredAtom2622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04449
  ] at hbad
  tauto

theorem fin15Anchored_clause19379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom2623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08545
  ] at hbad
  tauto

theorem fin15Anchored_clause19380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom2623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08545
  ] at hbad
  tauto

theorem fin15Anchored_clause19381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom2623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08545
  ] at hbad
  tauto

theorem fin15Anchored_clause19382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2623 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom2623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08545
  ] at hbad
  tauto

theorem fin15Anchored_clause19383 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2623 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom0706 Fin15AnchoredAtom0719
    Fin15AnchoredAtom0747 Fin15AnchoredAtom1622 Fin15AnchoredAtom2623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08545
  ] at hbad
  tauto

theorem fin15Anchored_clause19384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom2624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16737
  ] at hbad
  tauto

theorem fin15Anchored_clause19385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16737
  ] at hbad
  tauto

theorem fin15Anchored_clause19386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0720 Fin15AnchoredAtom2624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16737
  ] at hbad
  tauto

theorem fin15Anchored_clause19387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0748 Fin15AnchoredAtom2624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16737
  ] at hbad
  tauto

theorem fin15Anchored_clause19388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2624 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1623 Fin15AnchoredAtom2624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16737
  ] at hbad
  tauto

theorem fin15Anchored_clause19389 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2624 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom0707 Fin15AnchoredAtom0720
    Fin15AnchoredAtom0748 Fin15AnchoredAtom1623 Fin15AnchoredAtom2624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16737
  ] at hbad
  tauto

theorem fin15Anchored_clause19390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2625 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01633
  ] at hbad
  tauto

theorem fin15Anchored_clause19391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2625 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01633
  ] at hbad
  tauto

theorem fin15Anchored_clause19392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2625 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01633
  ] at hbad
  tauto

theorem fin15Anchored_clause19393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2625 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01633
  ] at hbad
  tauto

theorem fin15Anchored_clause19394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2625 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom2625 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01633
  ] at hbad
  tauto

theorem fin15Anchored_clause19395 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2625 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom0703 Fin15AnchoredAtom0721
    Fin15AnchoredAtom0749 Fin15AnchoredAtom1624 Fin15AnchoredAtom2625 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01633
  ] at hbad
  tauto

theorem fin15Anchored_clause19396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2626 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02657
  ] at hbad
  tauto

theorem fin15Anchored_clause19397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom0704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0704 Fin15AnchoredAtom2626 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02657
  ] at hbad
  tauto

theorem fin15Anchored_clause19398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom0722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0722 Fin15AnchoredAtom2626 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02657
  ] at hbad
  tauto

theorem fin15Anchored_clause19399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2626 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02657
  ] at hbad
  tauto

theorem fin15Anchored_clause19400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2626 chi ∧
      ¬Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1625 Fin15AnchoredAtom2626 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02657
  ] at hbad
  tauto

theorem fin15Anchored_clause19401 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2626 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom0704 Fin15AnchoredAtom0722
    Fin15AnchoredAtom0750 Fin15AnchoredAtom1625 Fin15AnchoredAtom2626 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02657
  ] at hbad
  tauto

theorem fin15Anchored_clause19402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04705
  ] at hbad
  tauto

theorem fin15Anchored_clause19403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04705
  ] at hbad
  tauto

theorem fin15Anchored_clause19404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04705
  ] at hbad
  tauto

theorem fin15Anchored_clause19405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04705
  ] at hbad
  tauto

theorem fin15Anchored_clause19406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2627 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom2627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04705
  ] at hbad
  tauto

theorem fin15Anchored_clause19407 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2627 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom0705 Fin15AnchoredAtom0723
    Fin15AnchoredAtom0751 Fin15AnchoredAtom1626 Fin15AnchoredAtom2627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04705
  ] at hbad
  tauto

theorem fin15Anchored_clause19408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08801
  ] at hbad
  tauto

theorem fin15Anchored_clause19409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom2628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08801
  ] at hbad
  tauto

theorem fin15Anchored_clause19410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08801
  ] at hbad
  tauto

theorem fin15Anchored_clause19411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08801
  ] at hbad
  tauto

theorem fin15Anchored_clause19412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2628 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom2628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08801
  ] at hbad
  tauto

theorem fin15Anchored_clause19413 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2628 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom0706 Fin15AnchoredAtom0724
    Fin15AnchoredAtom0752 Fin15AnchoredAtom1627 Fin15AnchoredAtom2628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08801
  ] at hbad
  tauto

theorem fin15Anchored_clause19414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2629 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16993
  ] at hbad
  tauto

theorem fin15Anchored_clause19415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2629 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16993
  ] at hbad
  tauto

theorem fin15Anchored_clause19416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2629 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16993
  ] at hbad
  tauto

theorem fin15Anchored_clause19417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2629 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16993
  ] at hbad
  tauto

theorem fin15Anchored_clause19418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2629 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom2629 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16993
  ] at hbad
  tauto

theorem fin15Anchored_clause19419 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2629 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom0707 Fin15AnchoredAtom0725
    Fin15AnchoredAtom0753 Fin15AnchoredAtom1628 Fin15AnchoredAtom2629 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16993
  ] at hbad
  tauto

theorem fin15Anchored_clause19420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03169
  ] at hbad
  tauto

theorem fin15Anchored_clause19421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom0704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0704 Fin15AnchoredAtom2630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03169
  ] at hbad
  tauto

theorem fin15Anchored_clause19422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom2630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03169
  ] at hbad
  tauto

theorem fin15Anchored_clause19423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom2630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03169
  ] at hbad
  tauto

theorem fin15Anchored_clause19424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2630 chi ∧
      ¬Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1629 Fin15AnchoredAtom2630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03169
  ] at hbad
  tauto

theorem fin15Anchored_clause19425 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2630 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom0704 Fin15AnchoredAtom0726
    Fin15AnchoredAtom0754 Fin15AnchoredAtom1629 Fin15AnchoredAtom2630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03169
  ] at hbad
  tauto

theorem fin15Anchored_clause19426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05217
  ] at hbad
  tauto

theorem fin15Anchored_clause19427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05217
  ] at hbad
  tauto

theorem fin15Anchored_clause19428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05217
  ] at hbad
  tauto

theorem fin15Anchored_clause19429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05217
  ] at hbad
  tauto

theorem fin15Anchored_clause19430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2631 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom2631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05217
  ] at hbad
  tauto

theorem fin15Anchored_clause19431 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2631 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom0705 Fin15AnchoredAtom0727
    Fin15AnchoredAtom0755 Fin15AnchoredAtom1630 Fin15AnchoredAtom2631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05217
  ] at hbad
  tauto

theorem fin15Anchored_clause19432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09313
  ] at hbad
  tauto

theorem fin15Anchored_clause19433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom2632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09313
  ] at hbad
  tauto

theorem fin15Anchored_clause19434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09313
  ] at hbad
  tauto

theorem fin15Anchored_clause19435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09313
  ] at hbad
  tauto

theorem fin15Anchored_clause19436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2632 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom2632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09313
  ] at hbad
  tauto

theorem fin15Anchored_clause19437 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2632 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom0706 Fin15AnchoredAtom0728
    Fin15AnchoredAtom0756 Fin15AnchoredAtom1631 Fin15AnchoredAtom2632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09313
  ] at hbad
  tauto

theorem fin15Anchored_clause19438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17505
  ] at hbad
  tauto

theorem fin15Anchored_clause19439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17505
  ] at hbad
  tauto

theorem fin15Anchored_clause19440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17505
  ] at hbad
  tauto

theorem fin15Anchored_clause19441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17505
  ] at hbad
  tauto

theorem fin15Anchored_clause19442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2633 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom2633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17505
  ] at hbad
  tauto

theorem fin15Anchored_clause19443 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2633 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom0707 Fin15AnchoredAtom0729
    Fin15AnchoredAtom0757 Fin15AnchoredAtom1632 Fin15AnchoredAtom2633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17505
  ] at hbad
  tauto

theorem fin15Anchored_clause19444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06241
  ] at hbad
  tauto

theorem fin15Anchored_clause19445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom2634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06241
  ] at hbad
  tauto

theorem fin15Anchored_clause19446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom0758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0758 Fin15AnchoredAtom2634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06241
  ] at hbad
  tauto

theorem fin15Anchored_clause19447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2634 chi ∧
      ¬Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1633 Fin15AnchoredAtom2634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06241
  ] at hbad
  tauto

theorem fin15Anchored_clause19448 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2634 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0704 Fin15AnchoredAtom0705 Fin15AnchoredAtom0730
    Fin15AnchoredAtom0758 Fin15AnchoredAtom1633 Fin15AnchoredAtom2634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06241
  ] at hbad
  tauto

theorem fin15Anchored_clause19449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2635 chi ∧
      ¬Fin15AnchoredAtom1634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1634 Fin15AnchoredAtom2635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10337
  ] at hbad
  tauto

theorem fin15Anchored_clause19450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2635 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom1634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0704 Fin15AnchoredAtom0706 Fin15AnchoredAtom0731
    Fin15AnchoredAtom0759 Fin15AnchoredAtom1634 Fin15AnchoredAtom2635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10337
  ] at hbad
  tauto

theorem fin15Anchored_clause19451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2636 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18529
  ] at hbad
  tauto

theorem fin15Anchored_clause19452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2636 chi ∧
      ¬Fin15AnchoredAtom0732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0732 Fin15AnchoredAtom2636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18529
  ] at hbad
  tauto

theorem fin15Anchored_clause19453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2636 chi ∧
      ¬Fin15AnchoredAtom0760 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0760 Fin15AnchoredAtom2636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18529
  ] at hbad
  tauto

theorem fin15Anchored_clause19454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2636 chi ∧
      ¬Fin15AnchoredAtom1635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1635 Fin15AnchoredAtom2636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18529
  ] at hbad
  tauto

theorem fin15Anchored_clause19455 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2636 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom0760 chi ∧
      Fin15AnchoredAtom1635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0704 Fin15AnchoredAtom0707 Fin15AnchoredAtom0732
    Fin15AnchoredAtom0760 Fin15AnchoredAtom1635 Fin15AnchoredAtom2636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18529
  ] at hbad
  tauto

end ErdosSzekeres

end
