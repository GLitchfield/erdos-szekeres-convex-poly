module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 146. -/

theorem fin15Anchored_clause18688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2487 chi ∧
      Fin15AnchoredAtom0647 chi ∧
      Fin15AnchoredAtom0648 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0815 chi ∧
      Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0647 Fin15AnchoredAtom0648 Fin15AnchoredAtom0654
    Fin15AnchoredAtom0815 Fin15AnchoredAtom1486 Fin15AnchoredAtom2487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25609
  ] at hbad
  tauto

theorem fin15Anchored_clause18689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2488 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2488 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14345
  ] at hbad
  tauto

theorem fin15Anchored_clause18690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2488 chi ∧
      ¬Fin15AnchoredAtom0816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0816 Fin15AnchoredAtom2488 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14345
  ] at hbad
  tauto

theorem fin15Anchored_clause18691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2488 chi ∧
      ¬Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1487 Fin15AnchoredAtom2488 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14345
  ] at hbad
  tauto

theorem fin15Anchored_clause18692 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2488 chi ∧
      Fin15AnchoredAtom0649 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0816 chi ∧
      Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0649 Fin15AnchoredAtom0650 Fin15AnchoredAtom0652
    Fin15AnchoredAtom0816 Fin15AnchoredAtom1487 Fin15AnchoredAtom2488 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14345
  ] at hbad
  tauto

theorem fin15Anchored_clause18693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2489 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22537
  ] at hbad
  tauto

theorem fin15Anchored_clause18694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2490 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26633
  ] at hbad
  tauto

theorem fin15Anchored_clause18695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2490 chi ∧
      ¬Fin15AnchoredAtom1489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1489 Fin15AnchoredAtom2490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26633
  ] at hbad
  tauto

theorem fin15Anchored_clause18696 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2490 chi ∧
      Fin15AnchoredAtom0650 chi ∧
      Fin15AnchoredAtom0651 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0818 chi ∧
      Fin15AnchoredAtom1489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0650 Fin15AnchoredAtom0651 Fin15AnchoredAtom0654
    Fin15AnchoredAtom0818 Fin15AnchoredAtom1489 Fin15AnchoredAtom2490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26633
  ] at hbad
  tauto

theorem fin15Anchored_clause18697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom0652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom2491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28681
  ] at hbad
  tauto

theorem fin15Anchored_clause18698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom0653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0653 Fin15AnchoredAtom2491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28681
  ] at hbad
  tauto

theorem fin15Anchored_clause18699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom0654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0654 Fin15AnchoredAtom2491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28681
  ] at hbad
  tauto

theorem fin15Anchored_clause18700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom0819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0819 Fin15AnchoredAtom2491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28681
  ] at hbad
  tauto

theorem fin15Anchored_clause18701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2491 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom2491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28681
  ] at hbad
  tauto

theorem fin15Anchored_clause18702 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2491 chi ∧
      Fin15AnchoredAtom0652 chi ∧
      Fin15AnchoredAtom0653 chi ∧
      Fin15AnchoredAtom0654 chi ∧
      Fin15AnchoredAtom0819 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0652 Fin15AnchoredAtom0653 Fin15AnchoredAtom0654
    Fin15AnchoredAtom0819 Fin15AnchoredAtom1490 Fin15AnchoredAtom2491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28681
  ] at hbad
  tauto

theorem fin15Anchored_clause18703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00241
  ] at hbad
  tauto

theorem fin15Anchored_clause18704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00241
  ] at hbad
  tauto

theorem fin15Anchored_clause18705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00241
  ] at hbad
  tauto

theorem fin15Anchored_clause18706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom0700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0700 Fin15AnchoredAtom2492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00241
  ] at hbad
  tauto

theorem fin15Anchored_clause18707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2492 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom2492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00241
  ] at hbad
  tauto

theorem fin15Anchored_clause18708 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2492 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0700 chi ∧
      Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom0656 Fin15AnchoredAtom0664
    Fin15AnchoredAtom0700 Fin15AnchoredAtom1491 Fin15AnchoredAtom2492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00241
  ] at hbad
  tauto

theorem fin15Anchored_clause18709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00369
  ] at hbad
  tauto

theorem fin15Anchored_clause18710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom2493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00369
  ] at hbad
  tauto

theorem fin15Anchored_clause18711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom2493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00369
  ] at hbad
  tauto

theorem fin15Anchored_clause18712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom0701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0701 Fin15AnchoredAtom2493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00369
  ] at hbad
  tauto

theorem fin15Anchored_clause18713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2493 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom2493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00369
  ] at hbad
  tauto

theorem fin15Anchored_clause18714 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2493 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0701 chi ∧
      Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom0657 Fin15AnchoredAtom0665
    Fin15AnchoredAtom0701 Fin15AnchoredAtom1492 Fin15AnchoredAtom2493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00369
  ] at hbad
  tauto

theorem fin15Anchored_clause18715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2494 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00625
  ] at hbad
  tauto

theorem fin15Anchored_clause18716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2494 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00625
  ] at hbad
  tauto

theorem fin15Anchored_clause18717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2494 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00625
  ] at hbad
  tauto

theorem fin15Anchored_clause18718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom0702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0702 Fin15AnchoredAtom2494 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00625
  ] at hbad
  tauto

theorem fin15Anchored_clause18719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2494 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom2494 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00625
  ] at hbad
  tauto

theorem fin15Anchored_clause18720 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2494 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0702 chi ∧
      Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom0658 Fin15AnchoredAtom0666
    Fin15AnchoredAtom0702 Fin15AnchoredAtom1493 Fin15AnchoredAtom2494 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00625
  ] at hbad
  tauto

theorem fin15Anchored_clause18721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01137
  ] at hbad
  tauto

theorem fin15Anchored_clause18722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01137
  ] at hbad
  tauto

theorem fin15Anchored_clause18723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01137
  ] at hbad
  tauto

theorem fin15Anchored_clause18724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom0703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0703 Fin15AnchoredAtom2495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01137
  ] at hbad
  tauto

theorem fin15Anchored_clause18725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2495 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom2495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01137
  ] at hbad
  tauto

theorem fin15Anchored_clause18726 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2495 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0703 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom0659 Fin15AnchoredAtom0667
    Fin15AnchoredAtom0703 Fin15AnchoredAtom1494 Fin15AnchoredAtom2495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01137
  ] at hbad
  tauto

theorem fin15Anchored_clause18727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2496 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02161
  ] at hbad
  tauto

theorem fin15Anchored_clause18728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2496 chi ∧
      ¬Fin15AnchoredAtom0704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0704 Fin15AnchoredAtom2496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02161
  ] at hbad
  tauto

theorem fin15Anchored_clause18729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2496 chi ∧
      ¬Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1495 Fin15AnchoredAtom2496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02161
  ] at hbad
  tauto

theorem fin15Anchored_clause18730 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2496 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0704 chi ∧
      Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom0660 Fin15AnchoredAtom0668
    Fin15AnchoredAtom0704 Fin15AnchoredAtom1495 Fin15AnchoredAtom2496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02161
  ] at hbad
  tauto

theorem fin15Anchored_clause18731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04209
  ] at hbad
  tauto

theorem fin15Anchored_clause18732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04209
  ] at hbad
  tauto

theorem fin15Anchored_clause18733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom2497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04209
  ] at hbad
  tauto

theorem fin15Anchored_clause18734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04209
  ] at hbad
  tauto

theorem fin15Anchored_clause18735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2497 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom2497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04209
  ] at hbad
  tauto

theorem fin15Anchored_clause18736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2497 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom0661 Fin15AnchoredAtom0669
    Fin15AnchoredAtom0705 Fin15AnchoredAtom1496 Fin15AnchoredAtom2497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04209
  ] at hbad
  tauto

theorem fin15Anchored_clause18737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08305
  ] at hbad
  tauto

theorem fin15Anchored_clause18738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom2498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08305
  ] at hbad
  tauto

theorem fin15Anchored_clause18739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom2498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08305
  ] at hbad
  tauto

theorem fin15Anchored_clause18740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom2498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08305
  ] at hbad
  tauto

theorem fin15Anchored_clause18741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2498 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom2498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08305
  ] at hbad
  tauto

theorem fin15Anchored_clause18742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2498 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom0662 Fin15AnchoredAtom0670
    Fin15AnchoredAtom0706 Fin15AnchoredAtom1497 Fin15AnchoredAtom2498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08305
  ] at hbad
  tauto

theorem fin15Anchored_clause18743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom0655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom2499 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16497
  ] at hbad
  tauto

theorem fin15Anchored_clause18744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom2499 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16497
  ] at hbad
  tauto

theorem fin15Anchored_clause18745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2499 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16497
  ] at hbad
  tauto

theorem fin15Anchored_clause18746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2499 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16497
  ] at hbad
  tauto

theorem fin15Anchored_clause18747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2499 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom2499 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16497
  ] at hbad
  tauto

theorem fin15Anchored_clause18748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2499 chi ∧
      Fin15AnchoredAtom0655 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0655 Fin15AnchoredAtom0663 Fin15AnchoredAtom0671
    Fin15AnchoredAtom0707 Fin15AnchoredAtom1498 Fin15AnchoredAtom2499 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16497
  ] at hbad
  tauto

theorem fin15Anchored_clause18749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2500 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00433
  ] at hbad
  tauto

theorem fin15Anchored_clause18750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom2500 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00433
  ] at hbad
  tauto

theorem fin15Anchored_clause18751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom2500 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00433
  ] at hbad
  tauto

theorem fin15Anchored_clause18752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom2500 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00433
  ] at hbad
  tauto

theorem fin15Anchored_clause18753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2500 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom2500 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00433
  ] at hbad
  tauto

theorem fin15Anchored_clause18754 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2500 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom0657 Fin15AnchoredAtom0672
    Fin15AnchoredAtom0708 Fin15AnchoredAtom1499 Fin15AnchoredAtom2500 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00433
  ] at hbad
  tauto

theorem fin15Anchored_clause18755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00689
  ] at hbad
  tauto

theorem fin15Anchored_clause18756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00689
  ] at hbad
  tauto

theorem fin15Anchored_clause18757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00689
  ] at hbad
  tauto

theorem fin15Anchored_clause18758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom2501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00689
  ] at hbad
  tauto

theorem fin15Anchored_clause18759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2501 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom2501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00689
  ] at hbad
  tauto

theorem fin15Anchored_clause18760 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2501 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom0658 Fin15AnchoredAtom0673
    Fin15AnchoredAtom0709 Fin15AnchoredAtom1500 Fin15AnchoredAtom2501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00689
  ] at hbad
  tauto

theorem fin15Anchored_clause18761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01201
  ] at hbad
  tauto

theorem fin15Anchored_clause18762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01201
  ] at hbad
  tauto

theorem fin15Anchored_clause18763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01201
  ] at hbad
  tauto

theorem fin15Anchored_clause18764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01201
  ] at hbad
  tauto

theorem fin15Anchored_clause18765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2502 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom2502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01201
  ] at hbad
  tauto

theorem fin15Anchored_clause18766 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2502 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom0659 Fin15AnchoredAtom0674
    Fin15AnchoredAtom0710 Fin15AnchoredAtom1501 Fin15AnchoredAtom2502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01201
  ] at hbad
  tauto

theorem fin15Anchored_clause18767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2503 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2503 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02225
  ] at hbad
  tauto

theorem fin15Anchored_clause18768 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2503 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom0660 Fin15AnchoredAtom0675
    Fin15AnchoredAtom0711 Fin15AnchoredAtom1502 Fin15AnchoredAtom2503 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02225
  ] at hbad
  tauto

theorem fin15Anchored_clause18769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04273
  ] at hbad
  tauto

theorem fin15Anchored_clause18770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04273
  ] at hbad
  tauto

theorem fin15Anchored_clause18771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04273
  ] at hbad
  tauto

theorem fin15Anchored_clause18772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04273
  ] at hbad
  tauto

theorem fin15Anchored_clause18773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2504 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom2504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04273
  ] at hbad
  tauto

theorem fin15Anchored_clause18774 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2504 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom0661 Fin15AnchoredAtom0676
    Fin15AnchoredAtom0712 Fin15AnchoredAtom1503 Fin15AnchoredAtom2504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04273
  ] at hbad
  tauto

theorem fin15Anchored_clause18775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08369
  ] at hbad
  tauto

theorem fin15Anchored_clause18776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom2505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08369
  ] at hbad
  tauto

theorem fin15Anchored_clause18777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom2505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08369
  ] at hbad
  tauto

theorem fin15Anchored_clause18778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08369
  ] at hbad
  tauto

theorem fin15Anchored_clause18779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2505 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom2505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08369
  ] at hbad
  tauto

theorem fin15Anchored_clause18780 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2505 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom0662 Fin15AnchoredAtom0677
    Fin15AnchoredAtom0713 Fin15AnchoredAtom1504 Fin15AnchoredAtom2505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08369
  ] at hbad
  tauto

theorem fin15Anchored_clause18781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom0656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom2506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16561
  ] at hbad
  tauto

theorem fin15Anchored_clause18782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom2506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16561
  ] at hbad
  tauto

theorem fin15Anchored_clause18783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16561
  ] at hbad
  tauto

theorem fin15Anchored_clause18784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16561
  ] at hbad
  tauto

theorem fin15Anchored_clause18785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2506 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom2506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16561
  ] at hbad
  tauto

theorem fin15Anchored_clause18786 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2506 chi ∧
      Fin15AnchoredAtom0656 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0656 Fin15AnchoredAtom0663 Fin15AnchoredAtom0678
    Fin15AnchoredAtom0714 Fin15AnchoredAtom1505 Fin15AnchoredAtom2506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16561
  ] at hbad
  tauto

theorem fin15Anchored_clause18787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom2507 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00817
  ] at hbad
  tauto

theorem fin15Anchored_clause18788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2507 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00817
  ] at hbad
  tauto

theorem fin15Anchored_clause18789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom2507 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00817
  ] at hbad
  tauto

theorem fin15Anchored_clause18790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2507 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00817
  ] at hbad
  tauto

theorem fin15Anchored_clause18791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2507 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom2507 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00817
  ] at hbad
  tauto

theorem fin15Anchored_clause18792 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2507 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom0658 Fin15AnchoredAtom0679
    Fin15AnchoredAtom0715 Fin15AnchoredAtom1506 Fin15AnchoredAtom2507 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00817
  ] at hbad
  tauto

theorem fin15Anchored_clause18793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom2508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01329
  ] at hbad
  tauto

theorem fin15Anchored_clause18794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01329
  ] at hbad
  tauto

theorem fin15Anchored_clause18795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom2508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01329
  ] at hbad
  tauto

theorem fin15Anchored_clause18796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom2508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01329
  ] at hbad
  tauto

theorem fin15Anchored_clause18797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2508 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom2508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01329
  ] at hbad
  tauto

theorem fin15Anchored_clause18798 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2508 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom0659 Fin15AnchoredAtom0680
    Fin15AnchoredAtom0716 Fin15AnchoredAtom1507 Fin15AnchoredAtom2508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01329
  ] at hbad
  tauto

theorem fin15Anchored_clause18799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom2510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04401
  ] at hbad
  tauto

theorem fin15Anchored_clause18800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04401
  ] at hbad
  tauto

theorem fin15Anchored_clause18801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom2510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04401
  ] at hbad
  tauto

theorem fin15Anchored_clause18802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom2510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04401
  ] at hbad
  tauto

theorem fin15Anchored_clause18803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2510 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom2510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04401
  ] at hbad
  tauto

theorem fin15Anchored_clause18804 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2510 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom0661 Fin15AnchoredAtom0682
    Fin15AnchoredAtom0718 Fin15AnchoredAtom1509 Fin15AnchoredAtom2510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04401
  ] at hbad
  tauto

theorem fin15Anchored_clause18805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom2511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08497
  ] at hbad
  tauto

theorem fin15Anchored_clause18806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom2511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08497
  ] at hbad
  tauto

theorem fin15Anchored_clause18807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom2511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08497
  ] at hbad
  tauto

theorem fin15Anchored_clause18808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom0719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0719 Fin15AnchoredAtom2511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08497
  ] at hbad
  tauto

theorem fin15Anchored_clause18809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2511 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom2511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08497
  ] at hbad
  tauto

theorem fin15Anchored_clause18810 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2511 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom0662 Fin15AnchoredAtom0683
    Fin15AnchoredAtom0719 Fin15AnchoredAtom1510 Fin15AnchoredAtom2511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08497
  ] at hbad
  tauto

theorem fin15Anchored_clause18811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom0657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom2512 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16689
  ] at hbad
  tauto

theorem fin15Anchored_clause18812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom2512 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16689
  ] at hbad
  tauto

theorem fin15Anchored_clause18813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom2512 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16689
  ] at hbad
  tauto

theorem fin15Anchored_clause18814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0720 Fin15AnchoredAtom2512 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16689
  ] at hbad
  tauto

theorem fin15Anchored_clause18815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2512 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1511 Fin15AnchoredAtom2512 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16689
  ] at hbad
  tauto

end ErdosSzekeres

end
