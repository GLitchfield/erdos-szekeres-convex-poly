module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 147. -/

theorem fin15Anchored_clause18816 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2512 chi ∧
      Fin15AnchoredAtom0657 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0657 Fin15AnchoredAtom0663 Fin15AnchoredAtom0684
    Fin15AnchoredAtom0720 Fin15AnchoredAtom1511 Fin15AnchoredAtom2512 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16689
  ] at hbad
  tauto

theorem fin15Anchored_clause18817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2513 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01585
  ] at hbad
  tauto

theorem fin15Anchored_clause18818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2513 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01585
  ] at hbad
  tauto

theorem fin15Anchored_clause18819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2513 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01585
  ] at hbad
  tauto

theorem fin15Anchored_clause18820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2513 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01585
  ] at hbad
  tauto

theorem fin15Anchored_clause18821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2513 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom2513 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01585
  ] at hbad
  tauto

theorem fin15Anchored_clause18822 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2513 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom0659 Fin15AnchoredAtom0685
    Fin15AnchoredAtom0721 Fin15AnchoredAtom1512 Fin15AnchoredAtom2513 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01585
  ] at hbad
  tauto

theorem fin15Anchored_clause18823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02609
  ] at hbad
  tauto

theorem fin15Anchored_clause18824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom0660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom2514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02609
  ] at hbad
  tauto

theorem fin15Anchored_clause18825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom0686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom2514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02609
  ] at hbad
  tauto

theorem fin15Anchored_clause18826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom0722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0722 Fin15AnchoredAtom2514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02609
  ] at hbad
  tauto

theorem fin15Anchored_clause18827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2514 chi ∧
      ¬Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1513 Fin15AnchoredAtom2514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02609
  ] at hbad
  tauto

theorem fin15Anchored_clause18828 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2514 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom0660 Fin15AnchoredAtom0686
    Fin15AnchoredAtom0722 Fin15AnchoredAtom1513 Fin15AnchoredAtom2514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02609
  ] at hbad
  tauto

theorem fin15Anchored_clause18829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04657
  ] at hbad
  tauto

theorem fin15Anchored_clause18830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04657
  ] at hbad
  tauto

theorem fin15Anchored_clause18831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04657
  ] at hbad
  tauto

theorem fin15Anchored_clause18832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04657
  ] at hbad
  tauto

theorem fin15Anchored_clause18833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2515 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom2515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04657
  ] at hbad
  tauto

theorem fin15Anchored_clause18834 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2515 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom0661 Fin15AnchoredAtom0687
    Fin15AnchoredAtom0723 Fin15AnchoredAtom1514 Fin15AnchoredAtom2515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04657
  ] at hbad
  tauto

theorem fin15Anchored_clause18835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08753
  ] at hbad
  tauto

theorem fin15Anchored_clause18836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom2516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08753
  ] at hbad
  tauto

theorem fin15Anchored_clause18837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom2516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08753
  ] at hbad
  tauto

theorem fin15Anchored_clause18838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08753
  ] at hbad
  tauto

theorem fin15Anchored_clause18839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2516 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom2516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08753
  ] at hbad
  tauto

theorem fin15Anchored_clause18840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2516 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom0662 Fin15AnchoredAtom0688
    Fin15AnchoredAtom0724 Fin15AnchoredAtom1515 Fin15AnchoredAtom2516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08753
  ] at hbad
  tauto

theorem fin15Anchored_clause18841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom0658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom2517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16945
  ] at hbad
  tauto

theorem fin15Anchored_clause18842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom2517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16945
  ] at hbad
  tauto

theorem fin15Anchored_clause18843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16945
  ] at hbad
  tauto

theorem fin15Anchored_clause18844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16945
  ] at hbad
  tauto

theorem fin15Anchored_clause18845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2517 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom2517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16945
  ] at hbad
  tauto

theorem fin15Anchored_clause18846 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2517 chi ∧
      Fin15AnchoredAtom0658 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0658 Fin15AnchoredAtom0663 Fin15AnchoredAtom0689
    Fin15AnchoredAtom0725 Fin15AnchoredAtom1516 Fin15AnchoredAtom2517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16945
  ] at hbad
  tauto

theorem fin15Anchored_clause18847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03121
  ] at hbad
  tauto

theorem fin15Anchored_clause18848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom0660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom2518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03121
  ] at hbad
  tauto

theorem fin15Anchored_clause18849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom2518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03121
  ] at hbad
  tauto

theorem fin15Anchored_clause18850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom2518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03121
  ] at hbad
  tauto

theorem fin15Anchored_clause18851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2518 chi ∧
      ¬Fin15AnchoredAtom1517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1517 Fin15AnchoredAtom2518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03121
  ] at hbad
  tauto

theorem fin15Anchored_clause18852 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2518 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom1517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom0660 Fin15AnchoredAtom0690
    Fin15AnchoredAtom0726 Fin15AnchoredAtom1517 Fin15AnchoredAtom2518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03121
  ] at hbad
  tauto

theorem fin15Anchored_clause18853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05169
  ] at hbad
  tauto

theorem fin15Anchored_clause18854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05169
  ] at hbad
  tauto

theorem fin15Anchored_clause18855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05169
  ] at hbad
  tauto

theorem fin15Anchored_clause18856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05169
  ] at hbad
  tauto

theorem fin15Anchored_clause18857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2519 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom2519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05169
  ] at hbad
  tauto

theorem fin15Anchored_clause18858 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2519 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom0661 Fin15AnchoredAtom0691
    Fin15AnchoredAtom0727 Fin15AnchoredAtom1518 Fin15AnchoredAtom2519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05169
  ] at hbad
  tauto

theorem fin15Anchored_clause18859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09265
  ] at hbad
  tauto

theorem fin15Anchored_clause18860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom2520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09265
  ] at hbad
  tauto

theorem fin15Anchored_clause18861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09265
  ] at hbad
  tauto

theorem fin15Anchored_clause18862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09265
  ] at hbad
  tauto

theorem fin15Anchored_clause18863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2520 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom2520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09265
  ] at hbad
  tauto

theorem fin15Anchored_clause18864 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2520 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom0662 Fin15AnchoredAtom0692
    Fin15AnchoredAtom0728 Fin15AnchoredAtom1519 Fin15AnchoredAtom2520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09265
  ] at hbad
  tauto

theorem fin15Anchored_clause18865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom0659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom2521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17457
  ] at hbad
  tauto

theorem fin15Anchored_clause18866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom2521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17457
  ] at hbad
  tauto

theorem fin15Anchored_clause18867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17457
  ] at hbad
  tauto

theorem fin15Anchored_clause18868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17457
  ] at hbad
  tauto

theorem fin15Anchored_clause18869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2521 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom2521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17457
  ] at hbad
  tauto

theorem fin15Anchored_clause18870 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2521 chi ∧
      Fin15AnchoredAtom0659 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0659 Fin15AnchoredAtom0663 Fin15AnchoredAtom0693
    Fin15AnchoredAtom0729 Fin15AnchoredAtom1520 Fin15AnchoredAtom2521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17457
  ] at hbad
  tauto

theorem fin15Anchored_clause18871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom0660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom2522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06193
  ] at hbad
  tauto

theorem fin15Anchored_clause18872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06193
  ] at hbad
  tauto

theorem fin15Anchored_clause18873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom2522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06193
  ] at hbad
  tauto

theorem fin15Anchored_clause18874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom2522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06193
  ] at hbad
  tauto

theorem fin15Anchored_clause18875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2522 chi ∧
      ¬Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1521 Fin15AnchoredAtom2522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06193
  ] at hbad
  tauto

theorem fin15Anchored_clause18876 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2522 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom1521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom0661 Fin15AnchoredAtom0694
    Fin15AnchoredAtom0730 Fin15AnchoredAtom1521 Fin15AnchoredAtom2522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06193
  ] at hbad
  tauto

theorem fin15Anchored_clause18877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2523 chi ∧
      ¬Fin15AnchoredAtom1522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1522 Fin15AnchoredAtom2523 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10289
  ] at hbad
  tauto

theorem fin15Anchored_clause18878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2523 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom1522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom0662 Fin15AnchoredAtom0695
    Fin15AnchoredAtom0731 Fin15AnchoredAtom1522 Fin15AnchoredAtom2523 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10289
  ] at hbad
  tauto

theorem fin15Anchored_clause18879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2524 chi ∧
      ¬Fin15AnchoredAtom0660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom2524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18481
  ] at hbad
  tauto

theorem fin15Anchored_clause18880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2524 chi ∧
      ¬Fin15AnchoredAtom1523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1523 Fin15AnchoredAtom2524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18481
  ] at hbad
  tauto

theorem fin15Anchored_clause18881 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2524 chi ∧
      Fin15AnchoredAtom0660 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0696 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom1523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0660 Fin15AnchoredAtom0663 Fin15AnchoredAtom0696
    Fin15AnchoredAtom0732 Fin15AnchoredAtom1523 Fin15AnchoredAtom2524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18481
  ] at hbad
  tauto

theorem fin15Anchored_clause18882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12337
  ] at hbad
  tauto

theorem fin15Anchored_clause18883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom2525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12337
  ] at hbad
  tauto

theorem fin15Anchored_clause18884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12337
  ] at hbad
  tauto

theorem fin15Anchored_clause18885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12337
  ] at hbad
  tauto

theorem fin15Anchored_clause18886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2525 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom2525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12337
  ] at hbad
  tauto

theorem fin15Anchored_clause18887 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2525 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom0662 Fin15AnchoredAtom0697
    Fin15AnchoredAtom0733 Fin15AnchoredAtom1524 Fin15AnchoredAtom2525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12337
  ] at hbad
  tauto

theorem fin15Anchored_clause18888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom0661 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom2526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20529
  ] at hbad
  tauto

theorem fin15Anchored_clause18889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom2526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20529
  ] at hbad
  tauto

theorem fin15Anchored_clause18890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom2526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20529
  ] at hbad
  tauto

theorem fin15Anchored_clause18891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20529
  ] at hbad
  tauto

theorem fin15Anchored_clause18892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2526 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom2526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20529
  ] at hbad
  tauto

theorem fin15Anchored_clause18893 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2526 chi ∧
      Fin15AnchoredAtom0661 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0661 Fin15AnchoredAtom0663 Fin15AnchoredAtom0698
    Fin15AnchoredAtom0734 Fin15AnchoredAtom1525 Fin15AnchoredAtom2526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20529
  ] at hbad
  tauto

theorem fin15Anchored_clause18894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom0662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom2527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24625
  ] at hbad
  tauto

theorem fin15Anchored_clause18895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom0663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0663 Fin15AnchoredAtom2527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24625
  ] at hbad
  tauto

theorem fin15Anchored_clause18896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom2527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24625
  ] at hbad
  tauto

theorem fin15Anchored_clause18897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24625
  ] at hbad
  tauto

theorem fin15Anchored_clause18898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2527 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom2527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24625
  ] at hbad
  tauto

theorem fin15Anchored_clause18899 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2527 chi ∧
      Fin15AnchoredAtom0662 chi ∧
      Fin15AnchoredAtom0663 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0662 Fin15AnchoredAtom0663 Fin15AnchoredAtom0699
    Fin15AnchoredAtom0735 Fin15AnchoredAtom1526 Fin15AnchoredAtom2527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24625
  ] at hbad
  tauto

theorem fin15Anchored_clause18900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00465
  ] at hbad
  tauto

theorem fin15Anchored_clause18901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom2528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00465
  ] at hbad
  tauto

theorem fin15Anchored_clause18902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom2528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00465
  ] at hbad
  tauto

theorem fin15Anchored_clause18903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom0736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0736 Fin15AnchoredAtom2528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00465
  ] at hbad
  tauto

theorem fin15Anchored_clause18904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2528 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom2528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00465
  ] at hbad
  tauto

theorem fin15Anchored_clause18905 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2528 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0736 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom0665 Fin15AnchoredAtom0672
    Fin15AnchoredAtom0736 Fin15AnchoredAtom1527 Fin15AnchoredAtom2528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00465
  ] at hbad
  tauto

theorem fin15Anchored_clause18906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00721
  ] at hbad
  tauto

theorem fin15Anchored_clause18907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00721
  ] at hbad
  tauto

theorem fin15Anchored_clause18908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00721
  ] at hbad
  tauto

theorem fin15Anchored_clause18909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom0737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0737 Fin15AnchoredAtom2529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00721
  ] at hbad
  tauto

theorem fin15Anchored_clause18910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2529 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom2529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00721
  ] at hbad
  tauto

theorem fin15Anchored_clause18911 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2529 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0737 chi ∧
      Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom0666 Fin15AnchoredAtom0673
    Fin15AnchoredAtom0737 Fin15AnchoredAtom1528 Fin15AnchoredAtom2529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00721
  ] at hbad
  tauto

theorem fin15Anchored_clause18912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01233
  ] at hbad
  tauto

theorem fin15Anchored_clause18913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01233
  ] at hbad
  tauto

theorem fin15Anchored_clause18914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01233
  ] at hbad
  tauto

theorem fin15Anchored_clause18915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom0738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0738 Fin15AnchoredAtom2530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01233
  ] at hbad
  tauto

theorem fin15Anchored_clause18916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2530 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom2530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01233
  ] at hbad
  tauto

theorem fin15Anchored_clause18917 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2530 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0738 chi ∧
      Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom0667 Fin15AnchoredAtom0674
    Fin15AnchoredAtom0738 Fin15AnchoredAtom1529 Fin15AnchoredAtom2530 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01233
  ] at hbad
  tauto

theorem fin15Anchored_clause18918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02257
  ] at hbad
  tauto

theorem fin15Anchored_clause18919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom2531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02257
  ] at hbad
  tauto

theorem fin15Anchored_clause18920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom0675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0675 Fin15AnchoredAtom2531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02257
  ] at hbad
  tauto

theorem fin15Anchored_clause18921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom0739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0739 Fin15AnchoredAtom2531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02257
  ] at hbad
  tauto

theorem fin15Anchored_clause18922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2531 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1530 Fin15AnchoredAtom2531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02257
  ] at hbad
  tauto

theorem fin15Anchored_clause18923 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2531 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0739 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom0668 Fin15AnchoredAtom0675
    Fin15AnchoredAtom0739 Fin15AnchoredAtom1530 Fin15AnchoredAtom2531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02257
  ] at hbad
  tauto

theorem fin15Anchored_clause18924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04305
  ] at hbad
  tauto

theorem fin15Anchored_clause18925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom2532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04305
  ] at hbad
  tauto

theorem fin15Anchored_clause18926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04305
  ] at hbad
  tauto

theorem fin15Anchored_clause18927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom0740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0740 Fin15AnchoredAtom2532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04305
  ] at hbad
  tauto

theorem fin15Anchored_clause18928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2532 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom2532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04305
  ] at hbad
  tauto

theorem fin15Anchored_clause18929 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2532 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0740 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom0669 Fin15AnchoredAtom0676
    Fin15AnchoredAtom0740 Fin15AnchoredAtom1531 Fin15AnchoredAtom2532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04305
  ] at hbad
  tauto

theorem fin15Anchored_clause18930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08401
  ] at hbad
  tauto

theorem fin15Anchored_clause18931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom2533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08401
  ] at hbad
  tauto

theorem fin15Anchored_clause18932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom2533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08401
  ] at hbad
  tauto

theorem fin15Anchored_clause18933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom0741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0741 Fin15AnchoredAtom2533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08401
  ] at hbad
  tauto

theorem fin15Anchored_clause18934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2533 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom2533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08401
  ] at hbad
  tauto

theorem fin15Anchored_clause18935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2533 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0741 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom0670 Fin15AnchoredAtom0677
    Fin15AnchoredAtom0741 Fin15AnchoredAtom1532 Fin15AnchoredAtom2533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08401
  ] at hbad
  tauto

theorem fin15Anchored_clause18936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom0664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom2534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16593
  ] at hbad
  tauto

theorem fin15Anchored_clause18937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16593
  ] at hbad
  tauto

theorem fin15Anchored_clause18938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16593
  ] at hbad
  tauto

theorem fin15Anchored_clause18939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom0742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0742 Fin15AnchoredAtom2534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16593
  ] at hbad
  tauto

theorem fin15Anchored_clause18940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2534 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom2534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16593
  ] at hbad
  tauto

theorem fin15Anchored_clause18941 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2534 chi ∧
      Fin15AnchoredAtom0664 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0742 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0664 Fin15AnchoredAtom0671 Fin15AnchoredAtom0678
    Fin15AnchoredAtom0742 Fin15AnchoredAtom1533 Fin15AnchoredAtom2534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16593
  ] at hbad
  tauto

theorem fin15Anchored_clause18942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom2535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00849
  ] at hbad
  tauto

theorem fin15Anchored_clause18943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00849
  ] at hbad
  tauto

end ErdosSzekeres

end
