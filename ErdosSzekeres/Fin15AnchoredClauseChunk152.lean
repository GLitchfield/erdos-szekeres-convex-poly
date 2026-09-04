module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 152. -/

theorem fin15Anchored_clause19456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12385
  ] at hbad
  tauto

theorem fin15Anchored_clause19457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom2637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12385
  ] at hbad
  tauto

theorem fin15Anchored_clause19458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12385
  ] at hbad
  tauto

theorem fin15Anchored_clause19459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12385
  ] at hbad
  tauto

theorem fin15Anchored_clause19460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2637 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom2637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12385
  ] at hbad
  tauto

theorem fin15Anchored_clause19461 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2637 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom0706 Fin15AnchoredAtom0733
    Fin15AnchoredAtom0761 Fin15AnchoredAtom1636 Fin15AnchoredAtom2637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12385
  ] at hbad
  tauto

theorem fin15Anchored_clause19462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom0705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom2638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20577
  ] at hbad
  tauto

theorem fin15Anchored_clause19463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20577
  ] at hbad
  tauto

theorem fin15Anchored_clause19464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20577
  ] at hbad
  tauto

theorem fin15Anchored_clause19465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20577
  ] at hbad
  tauto

theorem fin15Anchored_clause19466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2638 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom2638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20577
  ] at hbad
  tauto

theorem fin15Anchored_clause19467 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2638 chi ∧
      Fin15AnchoredAtom0705 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0705 Fin15AnchoredAtom0707 Fin15AnchoredAtom0734
    Fin15AnchoredAtom0762 Fin15AnchoredAtom1637 Fin15AnchoredAtom2638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20577
  ] at hbad
  tauto

theorem fin15Anchored_clause19468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom0706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom2639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24673
  ] at hbad
  tauto

theorem fin15Anchored_clause19469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom0707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0707 Fin15AnchoredAtom2639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24673
  ] at hbad
  tauto

theorem fin15Anchored_clause19470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24673
  ] at hbad
  tauto

theorem fin15Anchored_clause19471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24673
  ] at hbad
  tauto

theorem fin15Anchored_clause19472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2639 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom2639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24673
  ] at hbad
  tauto

theorem fin15Anchored_clause19473 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2639 chi ∧
      Fin15AnchoredAtom0706 chi ∧
      Fin15AnchoredAtom0707 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0706 Fin15AnchoredAtom0707 Fin15AnchoredAtom0735
    Fin15AnchoredAtom0763 Fin15AnchoredAtom1638 Fin15AnchoredAtom2639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24673
  ] at hbad
  tauto

theorem fin15Anchored_clause19474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom2640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00929
  ] at hbad
  tauto

theorem fin15Anchored_clause19475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom2640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00929
  ] at hbad
  tauto

theorem fin15Anchored_clause19476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00929
  ] at hbad
  tauto

theorem fin15Anchored_clause19477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom2640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00929
  ] at hbad
  tauto

theorem fin15Anchored_clause19478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2640 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom2640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00929
  ] at hbad
  tauto

theorem fin15Anchored_clause19479 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2640 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom0709 Fin15AnchoredAtom0715
    Fin15AnchoredAtom0764 Fin15AnchoredAtom1639 Fin15AnchoredAtom2640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00929
  ] at hbad
  tauto

theorem fin15Anchored_clause19480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom2641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01441
  ] at hbad
  tauto

theorem fin15Anchored_clause19481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01441
  ] at hbad
  tauto

theorem fin15Anchored_clause19482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom2641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01441
  ] at hbad
  tauto

theorem fin15Anchored_clause19483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2641 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom2641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01441
  ] at hbad
  tauto

theorem fin15Anchored_clause19484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2641 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom0710 Fin15AnchoredAtom0716
    Fin15AnchoredAtom0765 Fin15AnchoredAtom1640 Fin15AnchoredAtom2641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01441
  ] at hbad
  tauto

theorem fin15Anchored_clause19485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom2643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04513
  ] at hbad
  tauto

theorem fin15Anchored_clause19486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04513
  ] at hbad
  tauto

theorem fin15Anchored_clause19487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom2643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04513
  ] at hbad
  tauto

theorem fin15Anchored_clause19488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2643 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom2643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04513
  ] at hbad
  tauto

theorem fin15Anchored_clause19489 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2643 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom0712 Fin15AnchoredAtom0718
    Fin15AnchoredAtom0767 Fin15AnchoredAtom1642 Fin15AnchoredAtom2643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04513
  ] at hbad
  tauto

theorem fin15Anchored_clause19490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom2644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08609
  ] at hbad
  tauto

theorem fin15Anchored_clause19491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08609
  ] at hbad
  tauto

theorem fin15Anchored_clause19492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom0719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0719 Fin15AnchoredAtom2644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08609
  ] at hbad
  tauto

theorem fin15Anchored_clause19493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0768 Fin15AnchoredAtom2644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08609
  ] at hbad
  tauto

theorem fin15Anchored_clause19494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2644 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom2644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08609
  ] at hbad
  tauto

theorem fin15Anchored_clause19495 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2644 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom0713 Fin15AnchoredAtom0719
    Fin15AnchoredAtom0768 Fin15AnchoredAtom1643 Fin15AnchoredAtom2644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08609
  ] at hbad
  tauto

theorem fin15Anchored_clause19496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom0708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom2645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16801
  ] at hbad
  tauto

theorem fin15Anchored_clause19497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16801
  ] at hbad
  tauto

theorem fin15Anchored_clause19498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0720 Fin15AnchoredAtom2645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16801
  ] at hbad
  tauto

theorem fin15Anchored_clause19499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0769 Fin15AnchoredAtom2645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16801
  ] at hbad
  tauto

theorem fin15Anchored_clause19500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2645 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1644 Fin15AnchoredAtom2645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16801
  ] at hbad
  tauto

theorem fin15Anchored_clause19501 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2645 chi ∧
      Fin15AnchoredAtom0708 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0708 Fin15AnchoredAtom0714 Fin15AnchoredAtom0720
    Fin15AnchoredAtom0769 Fin15AnchoredAtom1644 Fin15AnchoredAtom2645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16801
  ] at hbad
  tauto

theorem fin15Anchored_clause19502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom2646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01697
  ] at hbad
  tauto

theorem fin15Anchored_clause19503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01697
  ] at hbad
  tauto

theorem fin15Anchored_clause19504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01697
  ] at hbad
  tauto

theorem fin15Anchored_clause19505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01697
  ] at hbad
  tauto

theorem fin15Anchored_clause19506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2646 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom2646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01697
  ] at hbad
  tauto

theorem fin15Anchored_clause19507 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2646 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom0710 Fin15AnchoredAtom0721
    Fin15AnchoredAtom0770 Fin15AnchoredAtom1645 Fin15AnchoredAtom2646 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01697
  ] at hbad
  tauto

theorem fin15Anchored_clause19508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2647 chi ∧
      ¬Fin15AnchoredAtom0711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0711 Fin15AnchoredAtom2647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02721
  ] at hbad
  tauto

theorem fin15Anchored_clause19509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2647 chi ∧
      ¬Fin15AnchoredAtom0722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0722 Fin15AnchoredAtom2647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02721
  ] at hbad
  tauto

theorem fin15Anchored_clause19510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2647 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom2647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02721
  ] at hbad
  tauto

theorem fin15Anchored_clause19511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2647 chi ∧
      ¬Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1646 Fin15AnchoredAtom2647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02721
  ] at hbad
  tauto

theorem fin15Anchored_clause19512 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2647 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom0711 Fin15AnchoredAtom0722
    Fin15AnchoredAtom0771 Fin15AnchoredAtom1646 Fin15AnchoredAtom2647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02721
  ] at hbad
  tauto

theorem fin15Anchored_clause19513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom2648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04769
  ] at hbad
  tauto

theorem fin15Anchored_clause19514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04769
  ] at hbad
  tauto

theorem fin15Anchored_clause19515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04769
  ] at hbad
  tauto

theorem fin15Anchored_clause19516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04769
  ] at hbad
  tauto

theorem fin15Anchored_clause19517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2648 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom2648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04769
  ] at hbad
  tauto

theorem fin15Anchored_clause19518 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2648 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom0712 Fin15AnchoredAtom0723
    Fin15AnchoredAtom0772 Fin15AnchoredAtom1647 Fin15AnchoredAtom2648 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04769
  ] at hbad
  tauto

theorem fin15Anchored_clause19519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom2649 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08865
  ] at hbad
  tauto

theorem fin15Anchored_clause19520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2649 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08865
  ] at hbad
  tauto

theorem fin15Anchored_clause19521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2649 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08865
  ] at hbad
  tauto

theorem fin15Anchored_clause19522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2649 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08865
  ] at hbad
  tauto

theorem fin15Anchored_clause19523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2649 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom2649 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08865
  ] at hbad
  tauto

theorem fin15Anchored_clause19524 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2649 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom0713 Fin15AnchoredAtom0724
    Fin15AnchoredAtom0773 Fin15AnchoredAtom1648 Fin15AnchoredAtom2649 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08865
  ] at hbad
  tauto

theorem fin15Anchored_clause19525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom0709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom2650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17057
  ] at hbad
  tauto

theorem fin15Anchored_clause19526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17057
  ] at hbad
  tauto

theorem fin15Anchored_clause19527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17057
  ] at hbad
  tauto

theorem fin15Anchored_clause19528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17057
  ] at hbad
  tauto

theorem fin15Anchored_clause19529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2650 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom2650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17057
  ] at hbad
  tauto

theorem fin15Anchored_clause19530 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2650 chi ∧
      Fin15AnchoredAtom0709 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0709 Fin15AnchoredAtom0714 Fin15AnchoredAtom0725
    Fin15AnchoredAtom0774 Fin15AnchoredAtom1649 Fin15AnchoredAtom2650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17057
  ] at hbad
  tauto

theorem fin15Anchored_clause19531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03233
  ] at hbad
  tauto

theorem fin15Anchored_clause19532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom0711 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0711 Fin15AnchoredAtom2651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03233
  ] at hbad
  tauto

theorem fin15Anchored_clause19533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom2651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03233
  ] at hbad
  tauto

theorem fin15Anchored_clause19534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03233
  ] at hbad
  tauto

theorem fin15Anchored_clause19535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2651 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom2651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03233
  ] at hbad
  tauto

theorem fin15Anchored_clause19536 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2651 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom0711 Fin15AnchoredAtom0726
    Fin15AnchoredAtom0775 Fin15AnchoredAtom1650 Fin15AnchoredAtom2651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03233
  ] at hbad
  tauto

theorem fin15Anchored_clause19537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05281
  ] at hbad
  tauto

theorem fin15Anchored_clause19538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05281
  ] at hbad
  tauto

theorem fin15Anchored_clause19539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05281
  ] at hbad
  tauto

theorem fin15Anchored_clause19540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05281
  ] at hbad
  tauto

theorem fin15Anchored_clause19541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2652 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom2652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05281
  ] at hbad
  tauto

theorem fin15Anchored_clause19542 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2652 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom0712 Fin15AnchoredAtom0727
    Fin15AnchoredAtom0776 Fin15AnchoredAtom1651 Fin15AnchoredAtom2652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05281
  ] at hbad
  tauto

theorem fin15Anchored_clause19543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09377
  ] at hbad
  tauto

theorem fin15Anchored_clause19544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09377
  ] at hbad
  tauto

theorem fin15Anchored_clause19545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09377
  ] at hbad
  tauto

theorem fin15Anchored_clause19546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09377
  ] at hbad
  tauto

theorem fin15Anchored_clause19547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2653 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom2653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09377
  ] at hbad
  tauto

theorem fin15Anchored_clause19548 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2653 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom0713 Fin15AnchoredAtom0728
    Fin15AnchoredAtom0777 Fin15AnchoredAtom1652 Fin15AnchoredAtom2653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09377
  ] at hbad
  tauto

theorem fin15Anchored_clause19549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom0710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom2654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17569
  ] at hbad
  tauto

theorem fin15Anchored_clause19550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17569
  ] at hbad
  tauto

theorem fin15Anchored_clause19551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17569
  ] at hbad
  tauto

theorem fin15Anchored_clause19552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17569
  ] at hbad
  tauto

theorem fin15Anchored_clause19553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2654 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom2654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17569
  ] at hbad
  tauto

theorem fin15Anchored_clause19554 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2654 chi ∧
      Fin15AnchoredAtom0710 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0710 Fin15AnchoredAtom0714 Fin15AnchoredAtom0729
    Fin15AnchoredAtom0778 Fin15AnchoredAtom1653 Fin15AnchoredAtom2654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17569
  ] at hbad
  tauto

theorem fin15Anchored_clause19555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06305
  ] at hbad
  tauto

theorem fin15Anchored_clause19556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom2655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06305
  ] at hbad
  tauto

theorem fin15Anchored_clause19557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2655 chi ∧
      ¬Fin15AnchoredAtom0779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0779 Fin15AnchoredAtom2655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06305
  ] at hbad
  tauto

theorem fin15Anchored_clause19558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2655 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0711 Fin15AnchoredAtom0712 Fin15AnchoredAtom0730
    Fin15AnchoredAtom0779 Fin15AnchoredAtom1654 Fin15AnchoredAtom2655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06305
  ] at hbad
  tauto

theorem fin15Anchored_clause19559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2656 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10401
  ] at hbad
  tauto

theorem fin15Anchored_clause19560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2656 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0780 Fin15AnchoredAtom2656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10401
  ] at hbad
  tauto

theorem fin15Anchored_clause19561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2656 chi ∧
      ¬Fin15AnchoredAtom1655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1655 Fin15AnchoredAtom2656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10401
  ] at hbad
  tauto

theorem fin15Anchored_clause19562 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2656 chi ∧
      Fin15AnchoredAtom0711 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0780 chi ∧
      Fin15AnchoredAtom1655 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0711 Fin15AnchoredAtom0713 Fin15AnchoredAtom0731
    Fin15AnchoredAtom0780 Fin15AnchoredAtom1655 Fin15AnchoredAtom2656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10401
  ] at hbad
  tauto

theorem fin15Anchored_clause19563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18593
  ] at hbad
  tauto

theorem fin15Anchored_clause19564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom0732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0732 Fin15AnchoredAtom2657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18593
  ] at hbad
  tauto

theorem fin15Anchored_clause19565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2657 chi ∧
      ¬Fin15AnchoredAtom0781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0781 Fin15AnchoredAtom2657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18593
  ] at hbad
  tauto

theorem fin15Anchored_clause19566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12449
  ] at hbad
  tauto

theorem fin15Anchored_clause19567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12449
  ] at hbad
  tauto

theorem fin15Anchored_clause19568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12449
  ] at hbad
  tauto

theorem fin15Anchored_clause19569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12449
  ] at hbad
  tauto

theorem fin15Anchored_clause19570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2658 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom2658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12449
  ] at hbad
  tauto

theorem fin15Anchored_clause19571 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2658 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom0713 Fin15AnchoredAtom0733
    Fin15AnchoredAtom0782 Fin15AnchoredAtom1657 Fin15AnchoredAtom2658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12449
  ] at hbad
  tauto

theorem fin15Anchored_clause19572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom0712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom2659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20641
  ] at hbad
  tauto

theorem fin15Anchored_clause19573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20641
  ] at hbad
  tauto

theorem fin15Anchored_clause19574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20641
  ] at hbad
  tauto

theorem fin15Anchored_clause19575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20641
  ] at hbad
  tauto

theorem fin15Anchored_clause19576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2659 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom2659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20641
  ] at hbad
  tauto

theorem fin15Anchored_clause19577 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2659 chi ∧
      Fin15AnchoredAtom0712 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0712 Fin15AnchoredAtom0714 Fin15AnchoredAtom0734
    Fin15AnchoredAtom0783 Fin15AnchoredAtom1658 Fin15AnchoredAtom2659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20641
  ] at hbad
  tauto

theorem fin15Anchored_clause19578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom0713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom2660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24737
  ] at hbad
  tauto

theorem fin15Anchored_clause19579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom0714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0714 Fin15AnchoredAtom2660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24737
  ] at hbad
  tauto

theorem fin15Anchored_clause19580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24737
  ] at hbad
  tauto

theorem fin15Anchored_clause19581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24737
  ] at hbad
  tauto

theorem fin15Anchored_clause19582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2660 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom2660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24737
  ] at hbad
  tauto

theorem fin15Anchored_clause19583 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2660 chi ∧
      Fin15AnchoredAtom0713 chi ∧
      Fin15AnchoredAtom0714 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0713 Fin15AnchoredAtom0714 Fin15AnchoredAtom0735
    Fin15AnchoredAtom0784 Fin15AnchoredAtom1659 Fin15AnchoredAtom2660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24737
  ] at hbad
  tauto

end ErdosSzekeres

end
