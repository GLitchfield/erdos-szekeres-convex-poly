module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 145. -/

theorem fin15Anchored_clause18560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2457 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom2457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01801
  ] at hbad
  tauto

theorem fin15Anchored_clause18561 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2457 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom0635 Fin15AnchoredAtom0640
    Fin15AnchoredAtom0785 Fin15AnchoredAtom1456 Fin15AnchoredAtom2457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01801
  ] at hbad
  tauto

theorem fin15Anchored_clause18562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom2459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04873
  ] at hbad
  tauto

theorem fin15Anchored_clause18563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom2459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04873
  ] at hbad
  tauto

theorem fin15Anchored_clause18564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04873
  ] at hbad
  tauto

theorem fin15Anchored_clause18565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom2459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04873
  ] at hbad
  tauto

theorem fin15Anchored_clause18566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2459 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom2459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04873
  ] at hbad
  tauto

theorem fin15Anchored_clause18567 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2459 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom0637 Fin15AnchoredAtom0642
    Fin15AnchoredAtom0787 Fin15AnchoredAtom1458 Fin15AnchoredAtom2459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04873
  ] at hbad
  tauto

theorem fin15Anchored_clause18568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom2460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08969
  ] at hbad
  tauto

theorem fin15Anchored_clause18569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom2460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08969
  ] at hbad
  tauto

theorem fin15Anchored_clause18570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom2460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08969
  ] at hbad
  tauto

theorem fin15Anchored_clause18571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom2460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08969
  ] at hbad
  tauto

theorem fin15Anchored_clause18572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2460 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1459 Fin15AnchoredAtom2460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08969
  ] at hbad
  tauto

theorem fin15Anchored_clause18573 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2460 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom0638 Fin15AnchoredAtom0643
    Fin15AnchoredAtom0788 Fin15AnchoredAtom1459 Fin15AnchoredAtom2460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08969
  ] at hbad
  tauto

theorem fin15Anchored_clause18574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom0634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom2461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17161
  ] at hbad
  tauto

theorem fin15Anchored_clause18575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0639 Fin15AnchoredAtom2461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17161
  ] at hbad
  tauto

theorem fin15Anchored_clause18576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom2461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17161
  ] at hbad
  tauto

theorem fin15Anchored_clause18577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2461 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0789 Fin15AnchoredAtom2461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17161
  ] at hbad
  tauto

theorem fin15Anchored_clause18578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2461 chi ∧
      Fin15AnchoredAtom0634 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0634 Fin15AnchoredAtom0639 Fin15AnchoredAtom0644
    Fin15AnchoredAtom0789 Fin15AnchoredAtom1460 Fin15AnchoredAtom2461 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17161
  ] at hbad
  tauto

theorem fin15Anchored_clause18579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom2463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05385
  ] at hbad
  tauto

theorem fin15Anchored_clause18580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom2463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05385
  ] at hbad
  tauto

theorem fin15Anchored_clause18581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05385
  ] at hbad
  tauto

theorem fin15Anchored_clause18582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom2463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05385
  ] at hbad
  tauto

theorem fin15Anchored_clause18583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2463 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom2463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05385
  ] at hbad
  tauto

theorem fin15Anchored_clause18584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2463 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom0637 Fin15AnchoredAtom0646
    Fin15AnchoredAtom0791 Fin15AnchoredAtom1462 Fin15AnchoredAtom2463 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05385
  ] at hbad
  tauto

theorem fin15Anchored_clause18585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom2464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09481
  ] at hbad
  tauto

theorem fin15Anchored_clause18586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom2464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09481
  ] at hbad
  tauto

theorem fin15Anchored_clause18587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09481
  ] at hbad
  tauto

theorem fin15Anchored_clause18588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2464 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09481
  ] at hbad
  tauto

theorem fin15Anchored_clause18589 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2464 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom0638 Fin15AnchoredAtom0647
    Fin15AnchoredAtom0792 Fin15AnchoredAtom1463 Fin15AnchoredAtom2464 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09481
  ] at hbad
  tauto

theorem fin15Anchored_clause18590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom0635 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom2465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17673
  ] at hbad
  tauto

theorem fin15Anchored_clause18591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0639 Fin15AnchoredAtom2465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17673
  ] at hbad
  tauto

theorem fin15Anchored_clause18592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17673
  ] at hbad
  tauto

theorem fin15Anchored_clause18593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2465 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0793 Fin15AnchoredAtom2465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17673
  ] at hbad
  tauto

theorem fin15Anchored_clause18594 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2465 chi ∧
      Fin15AnchoredAtom0635 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0635 Fin15AnchoredAtom0639 Fin15AnchoredAtom0648
    Fin15AnchoredAtom0793 Fin15AnchoredAtom1464 Fin15AnchoredAtom2465 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17673
  ] at hbad
  tauto

theorem fin15Anchored_clause18595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom2469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12553
  ] at hbad
  tauto

theorem fin15Anchored_clause18596 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom2469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12553
  ] at hbad
  tauto

theorem fin15Anchored_clause18597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12553
  ] at hbad
  tauto

theorem fin15Anchored_clause18598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2469 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12553
  ] at hbad
  tauto

theorem fin15Anchored_clause18599 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2469 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom0638 Fin15AnchoredAtom0652
    Fin15AnchoredAtom0797 Fin15AnchoredAtom1468 Fin15AnchoredAtom2469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12553
  ] at hbad
  tauto

theorem fin15Anchored_clause18600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom0637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom2470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20745
  ] at hbad
  tauto

theorem fin15Anchored_clause18601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0639 Fin15AnchoredAtom2470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20745
  ] at hbad
  tauto

theorem fin15Anchored_clause18602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20745
  ] at hbad
  tauto

theorem fin15Anchored_clause18603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2470 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0798 Fin15AnchoredAtom2470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20745
  ] at hbad
  tauto

theorem fin15Anchored_clause18604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2470 chi ∧
      Fin15AnchoredAtom0637 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0637 Fin15AnchoredAtom0639 Fin15AnchoredAtom0653
    Fin15AnchoredAtom0798 Fin15AnchoredAtom1469 Fin15AnchoredAtom2470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20745
  ] at hbad
  tauto

theorem fin15Anchored_clause18605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom0638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom2471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24841
  ] at hbad
  tauto

theorem fin15Anchored_clause18606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom0639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0639 Fin15AnchoredAtom2471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24841
  ] at hbad
  tauto

theorem fin15Anchored_clause18607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24841
  ] at hbad
  tauto

theorem fin15Anchored_clause18608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0799 Fin15AnchoredAtom2471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24841
  ] at hbad
  tauto

theorem fin15Anchored_clause18609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2471 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1470 Fin15AnchoredAtom2471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24841
  ] at hbad
  tauto

theorem fin15Anchored_clause18610 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2471 chi ∧
      Fin15AnchoredAtom0638 chi ∧
      Fin15AnchoredAtom0639 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0638 Fin15AnchoredAtom0639 Fin15AnchoredAtom0654
    Fin15AnchoredAtom0799 Fin15AnchoredAtom1470 Fin15AnchoredAtom2471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24841
  ] at hbad
  tauto

theorem fin15Anchored_clause18611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2472 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03593
  ] at hbad
  tauto

theorem fin15Anchored_clause18612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2472 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2472 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03593
  ] at hbad
  tauto

theorem fin15Anchored_clause18613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05641
  ] at hbad
  tauto

theorem fin15Anchored_clause18614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05641
  ] at hbad
  tauto

theorem fin15Anchored_clause18615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05641
  ] at hbad
  tauto

theorem fin15Anchored_clause18616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05641
  ] at hbad
  tauto

theorem fin15Anchored_clause18617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2473 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom2473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05641
  ] at hbad
  tauto

theorem fin15Anchored_clause18618 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2473 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom0642 Fin15AnchoredAtom0646
    Fin15AnchoredAtom0801 Fin15AnchoredAtom1472 Fin15AnchoredAtom2473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05641
  ] at hbad
  tauto

theorem fin15Anchored_clause18619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09737
  ] at hbad
  tauto

theorem fin15Anchored_clause18620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom2474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09737
  ] at hbad
  tauto

theorem fin15Anchored_clause18621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09737
  ] at hbad
  tauto

theorem fin15Anchored_clause18622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09737
  ] at hbad
  tauto

theorem fin15Anchored_clause18623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2474 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom2474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09737
  ] at hbad
  tauto

theorem fin15Anchored_clause18624 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2474 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom0643 Fin15AnchoredAtom0647
    Fin15AnchoredAtom0802 Fin15AnchoredAtom1473 Fin15AnchoredAtom2474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09737
  ] at hbad
  tauto

theorem fin15Anchored_clause18625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom0640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom2475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17929
  ] at hbad
  tauto

theorem fin15Anchored_clause18626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom2475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17929
  ] at hbad
  tauto

theorem fin15Anchored_clause18627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17929
  ] at hbad
  tauto

theorem fin15Anchored_clause18628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17929
  ] at hbad
  tauto

theorem fin15Anchored_clause18629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2475 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom2475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17929
  ] at hbad
  tauto

theorem fin15Anchored_clause18630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2475 chi ∧
      Fin15AnchoredAtom0640 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0640 Fin15AnchoredAtom0644 Fin15AnchoredAtom0648
    Fin15AnchoredAtom0803 Fin15AnchoredAtom1474 Fin15AnchoredAtom2475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17929
  ] at hbad
  tauto

theorem fin15Anchored_clause18631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2476 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06665
  ] at hbad
  tauto

theorem fin15Anchored_clause18632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom0649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0649 Fin15AnchoredAtom2476 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06665
  ] at hbad
  tauto

theorem fin15Anchored_clause18633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2476 chi ∧
      ¬Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom2476 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06665
  ] at hbad
  tauto

theorem fin15Anchored_clause18634 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2476 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0641 Fin15AnchoredAtom0642 Fin15AnchoredAtom0649
    Fin15AnchoredAtom0804 Fin15AnchoredAtom1475 Fin15AnchoredAtom2476 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06665
  ] at hbad
  tauto

theorem fin15Anchored_clause18635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom0641 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0641 Fin15AnchoredAtom2477 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10761
  ] at hbad
  tauto

theorem fin15Anchored_clause18636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom0650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0650 Fin15AnchoredAtom2477 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10761
  ] at hbad
  tauto

theorem fin15Anchored_clause18637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom2477 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10761
  ] at hbad
  tauto

theorem fin15Anchored_clause18638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2477 chi ∧
      ¬Fin15AnchoredAtom1476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1476 Fin15AnchoredAtom2477 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10761
  ] at hbad
  tauto

theorem fin15Anchored_clause18639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2477 chi ∧
      Fin15AnchoredAtom0641 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0641 Fin15AnchoredAtom0643 Fin15AnchoredAtom0650
    Fin15AnchoredAtom0805 Fin15AnchoredAtom1476 Fin15AnchoredAtom2477 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10761
  ] at hbad
  tauto

theorem fin15Anchored_clause18640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2478 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0806 Fin15AnchoredAtom2478 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18953
  ] at hbad
  tauto

theorem fin15Anchored_clause18641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12809
  ] at hbad
  tauto

theorem fin15Anchored_clause18642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom2479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12809
  ] at hbad
  tauto

theorem fin15Anchored_clause18643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12809
  ] at hbad
  tauto

theorem fin15Anchored_clause18644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12809
  ] at hbad
  tauto

theorem fin15Anchored_clause18645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2479 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom2479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12809
  ] at hbad
  tauto

theorem fin15Anchored_clause18646 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2479 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom0643 Fin15AnchoredAtom0652
    Fin15AnchoredAtom0807 Fin15AnchoredAtom1478 Fin15AnchoredAtom2479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12809
  ] at hbad
  tauto

theorem fin15Anchored_clause18647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom0642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom2480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21001
  ] at hbad
  tauto

theorem fin15Anchored_clause18648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom2480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21001
  ] at hbad
  tauto

theorem fin15Anchored_clause18649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21001
  ] at hbad
  tauto

theorem fin15Anchored_clause18650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21001
  ] at hbad
  tauto

theorem fin15Anchored_clause18651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2480 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom2480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21001
  ] at hbad
  tauto

theorem fin15Anchored_clause18652 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2480 chi ∧
      Fin15AnchoredAtom0642 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0642 Fin15AnchoredAtom0644 Fin15AnchoredAtom0653
    Fin15AnchoredAtom0808 Fin15AnchoredAtom1479 Fin15AnchoredAtom2480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21001
  ] at hbad
  tauto

theorem fin15Anchored_clause18653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom0643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom2481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25097
  ] at hbad
  tauto

theorem fin15Anchored_clause18654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom0644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0644 Fin15AnchoredAtom2481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25097
  ] at hbad
  tauto

theorem fin15Anchored_clause18655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25097
  ] at hbad
  tauto

theorem fin15Anchored_clause18656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25097
  ] at hbad
  tauto

theorem fin15Anchored_clause18657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2481 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom2481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25097
  ] at hbad
  tauto

theorem fin15Anchored_clause18658 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2481 chi ∧
      Fin15AnchoredAtom0643 chi ∧
      Fin15AnchoredAtom0644 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0643 Fin15AnchoredAtom0644 Fin15AnchoredAtom0654
    Fin15AnchoredAtom0809 Fin15AnchoredAtom1480 Fin15AnchoredAtom2481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25097
  ] at hbad
  tauto

theorem fin15Anchored_clause18659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom0645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0645 Fin15AnchoredAtom2482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07177
  ] at hbad
  tauto

theorem fin15Anchored_clause18660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07177
  ] at hbad
  tauto

theorem fin15Anchored_clause18661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom0649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0649 Fin15AnchoredAtom2482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07177
  ] at hbad
  tauto

theorem fin15Anchored_clause18662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom2482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07177
  ] at hbad
  tauto

theorem fin15Anchored_clause18663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2482 chi ∧
      ¬Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1481 Fin15AnchoredAtom2482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07177
  ] at hbad
  tauto

theorem fin15Anchored_clause18664 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2482 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0645 Fin15AnchoredAtom0646 Fin15AnchoredAtom0649
    Fin15AnchoredAtom0810 Fin15AnchoredAtom1481 Fin15AnchoredAtom2482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07177
  ] at hbad
  tauto

theorem fin15Anchored_clause18665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom0645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0645 Fin15AnchoredAtom2483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11273
  ] at hbad
  tauto

theorem fin15Anchored_clause18666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11273
  ] at hbad
  tauto

theorem fin15Anchored_clause18667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11273
  ] at hbad
  tauto

theorem fin15Anchored_clause18668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2483 chi ∧
      ¬Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1482 Fin15AnchoredAtom2483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11273
  ] at hbad
  tauto

theorem fin15Anchored_clause18669 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2483 chi ∧
      Fin15AnchoredAtom0645 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0645 Fin15AnchoredAtom0647 Fin15AnchoredAtom0650
    Fin15AnchoredAtom0811 Fin15AnchoredAtom1482 Fin15AnchoredAtom2483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11273
  ] at hbad
  tauto

theorem fin15Anchored_clause18670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2484 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19465
  ] at hbad
  tauto

theorem fin15Anchored_clause18671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13321
  ] at hbad
  tauto

theorem fin15Anchored_clause18672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13321
  ] at hbad
  tauto

theorem fin15Anchored_clause18673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13321
  ] at hbad
  tauto

theorem fin15Anchored_clause18674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13321
  ] at hbad
  tauto

theorem fin15Anchored_clause18675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2485 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom2485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13321
  ] at hbad
  tauto

theorem fin15Anchored_clause18676 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2485 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0813 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom0647 Fin15AnchoredAtom0652
    Fin15AnchoredAtom0813 Fin15AnchoredAtom1484 Fin15AnchoredAtom2485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13321
  ] at hbad
  tauto

theorem fin15Anchored_clause18677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom0646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom2486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21513
  ] at hbad
  tauto

theorem fin15Anchored_clause18678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21513
  ] at hbad
  tauto

theorem fin15Anchored_clause18679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21513
  ] at hbad
  tauto

theorem fin15Anchored_clause18680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom0814 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0814 Fin15AnchoredAtom2486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21513
  ] at hbad
  tauto

theorem fin15Anchored_clause18681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2486 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom2486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21513
  ] at hbad
  tauto

theorem fin15Anchored_clause18682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2486 chi ∧
      Fin15AnchoredAtom0646 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0814 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0646 Fin15AnchoredAtom0648 Fin15AnchoredAtom0653
    Fin15AnchoredAtom0814 Fin15AnchoredAtom1485 Fin15AnchoredAtom2486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21513
  ] at hbad
  tauto

theorem fin15Anchored_clause18683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom0647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom2487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25609
  ] at hbad
  tauto

theorem fin15Anchored_clause18684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom0648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0648 Fin15AnchoredAtom2487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25609
  ] at hbad
  tauto

theorem fin15Anchored_clause18685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25609
  ] at hbad
  tauto

theorem fin15Anchored_clause18686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom0815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0815 Fin15AnchoredAtom2487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25609
  ] at hbad
  tauto

theorem fin15Anchored_clause18687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2487 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom2487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25609
  ] at hbad
  tauto

end ErdosSzekeres

end
