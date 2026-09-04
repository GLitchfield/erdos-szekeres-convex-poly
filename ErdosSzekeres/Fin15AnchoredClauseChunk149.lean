module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 149. -/

theorem fin15Anchored_clause19072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom2559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04497
  ] at hbad
  tauto

theorem fin15Anchored_clause19073 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2559 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0767 chi ∧
      Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom0676 Fin15AnchoredAtom0682
    Fin15AnchoredAtom0767 Fin15AnchoredAtom1558 Fin15AnchoredAtom2559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04497
  ] at hbad
  tauto

theorem fin15Anchored_clause19074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom2560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08593
  ] at hbad
  tauto

theorem fin15Anchored_clause19075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom2560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08593
  ] at hbad
  tauto

theorem fin15Anchored_clause19076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom2560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08593
  ] at hbad
  tauto

theorem fin15Anchored_clause19077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom0768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0768 Fin15AnchoredAtom2560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08593
  ] at hbad
  tauto

theorem fin15Anchored_clause19078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2560 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom2560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08593
  ] at hbad
  tauto

theorem fin15Anchored_clause19079 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2560 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0768 chi ∧
      Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom0677 Fin15AnchoredAtom0683
    Fin15AnchoredAtom0768 Fin15AnchoredAtom1559 Fin15AnchoredAtom2560 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08593
  ] at hbad
  tauto

theorem fin15Anchored_clause19080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom2561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16785
  ] at hbad
  tauto

theorem fin15Anchored_clause19081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16785
  ] at hbad
  tauto

theorem fin15Anchored_clause19082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom2561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16785
  ] at hbad
  tauto

theorem fin15Anchored_clause19083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom0769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0769 Fin15AnchoredAtom2561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16785
  ] at hbad
  tauto

theorem fin15Anchored_clause19084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2561 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom2561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16785
  ] at hbad
  tauto

theorem fin15Anchored_clause19085 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2561 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0769 chi ∧
      Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom0678 Fin15AnchoredAtom0684
    Fin15AnchoredAtom0769 Fin15AnchoredAtom1560 Fin15AnchoredAtom2561 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16785
  ] at hbad
  tauto

theorem fin15Anchored_clause19086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01681
  ] at hbad
  tauto

theorem fin15Anchored_clause19087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01681
  ] at hbad
  tauto

theorem fin15Anchored_clause19088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01681
  ] at hbad
  tauto

theorem fin15Anchored_clause19089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom0770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0770 Fin15AnchoredAtom2562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01681
  ] at hbad
  tauto

theorem fin15Anchored_clause19090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2562 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom2562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01681
  ] at hbad
  tauto

theorem fin15Anchored_clause19091 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2562 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0770 chi ∧
      Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom0674 Fin15AnchoredAtom0685
    Fin15AnchoredAtom0770 Fin15AnchoredAtom1561 Fin15AnchoredAtom2562 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01681
  ] at hbad
  tauto

theorem fin15Anchored_clause19092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2563 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02705
  ] at hbad
  tauto

theorem fin15Anchored_clause19093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom0675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0675 Fin15AnchoredAtom2563 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02705
  ] at hbad
  tauto

theorem fin15Anchored_clause19094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom0771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0771 Fin15AnchoredAtom2563 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02705
  ] at hbad
  tauto

theorem fin15Anchored_clause19095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2563 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1562 Fin15AnchoredAtom2563 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02705
  ] at hbad
  tauto

theorem fin15Anchored_clause19096 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2563 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0771 chi ∧
      Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom0675 Fin15AnchoredAtom0686
    Fin15AnchoredAtom0771 Fin15AnchoredAtom1562 Fin15AnchoredAtom2563 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02705
  ] at hbad
  tauto

theorem fin15Anchored_clause19097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2564 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04753
  ] at hbad
  tauto

theorem fin15Anchored_clause19098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2564 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04753
  ] at hbad
  tauto

theorem fin15Anchored_clause19099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2564 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04753
  ] at hbad
  tauto

theorem fin15Anchored_clause19100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom0772 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0772 Fin15AnchoredAtom2564 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04753
  ] at hbad
  tauto

theorem fin15Anchored_clause19101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2564 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom2564 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04753
  ] at hbad
  tauto

theorem fin15Anchored_clause19102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2564 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0772 chi ∧
      Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom0676 Fin15AnchoredAtom0687
    Fin15AnchoredAtom0772 Fin15AnchoredAtom1563 Fin15AnchoredAtom2564 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04753
  ] at hbad
  tauto

theorem fin15Anchored_clause19103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2565 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08849
  ] at hbad
  tauto

theorem fin15Anchored_clause19104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom2565 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08849
  ] at hbad
  tauto

theorem fin15Anchored_clause19105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom2565 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08849
  ] at hbad
  tauto

theorem fin15Anchored_clause19106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom0773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0773 Fin15AnchoredAtom2565 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08849
  ] at hbad
  tauto

theorem fin15Anchored_clause19107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2565 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom2565 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08849
  ] at hbad
  tauto

theorem fin15Anchored_clause19108 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2565 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0773 chi ∧
      Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom0677 Fin15AnchoredAtom0688
    Fin15AnchoredAtom0773 Fin15AnchoredAtom1564 Fin15AnchoredAtom2565 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08849
  ] at hbad
  tauto

theorem fin15Anchored_clause19109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17041
  ] at hbad
  tauto

theorem fin15Anchored_clause19110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17041
  ] at hbad
  tauto

theorem fin15Anchored_clause19111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17041
  ] at hbad
  tauto

theorem fin15Anchored_clause19112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom0774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0774 Fin15AnchoredAtom2566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17041
  ] at hbad
  tauto

theorem fin15Anchored_clause19113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2566 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom2566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17041
  ] at hbad
  tauto

theorem fin15Anchored_clause19114 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2566 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom0678 Fin15AnchoredAtom0689
    Fin15AnchoredAtom0774 Fin15AnchoredAtom1565 Fin15AnchoredAtom2566 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17041
  ] at hbad
  tauto

theorem fin15Anchored_clause19115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03217
  ] at hbad
  tauto

theorem fin15Anchored_clause19116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom2567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03217
  ] at hbad
  tauto

theorem fin15Anchored_clause19117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2567 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03217
  ] at hbad
  tauto

theorem fin15Anchored_clause19118 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2567 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0775 chi ∧
      Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom0675 Fin15AnchoredAtom0690
    Fin15AnchoredAtom0775 Fin15AnchoredAtom1566 Fin15AnchoredAtom2567 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03217
  ] at hbad
  tauto

theorem fin15Anchored_clause19119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2568 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05265
  ] at hbad
  tauto

theorem fin15Anchored_clause19120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2568 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05265
  ] at hbad
  tauto

theorem fin15Anchored_clause19121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2568 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05265
  ] at hbad
  tauto

theorem fin15Anchored_clause19122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2568 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05265
  ] at hbad
  tauto

theorem fin15Anchored_clause19123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2568 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom2568 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05265
  ] at hbad
  tauto

theorem fin15Anchored_clause19124 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2568 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom0676 Fin15AnchoredAtom0691
    Fin15AnchoredAtom0776 Fin15AnchoredAtom1567 Fin15AnchoredAtom2568 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05265
  ] at hbad
  tauto

theorem fin15Anchored_clause19125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09361
  ] at hbad
  tauto

theorem fin15Anchored_clause19126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom2569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09361
  ] at hbad
  tauto

theorem fin15Anchored_clause19127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09361
  ] at hbad
  tauto

theorem fin15Anchored_clause19128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09361
  ] at hbad
  tauto

theorem fin15Anchored_clause19129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2569 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom2569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09361
  ] at hbad
  tauto

theorem fin15Anchored_clause19130 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2569 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom0677 Fin15AnchoredAtom0692
    Fin15AnchoredAtom0777 Fin15AnchoredAtom1568 Fin15AnchoredAtom2569 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09361
  ] at hbad
  tauto

theorem fin15Anchored_clause19131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17553
  ] at hbad
  tauto

theorem fin15Anchored_clause19132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17553
  ] at hbad
  tauto

theorem fin15Anchored_clause19133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17553
  ] at hbad
  tauto

theorem fin15Anchored_clause19134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17553
  ] at hbad
  tauto

theorem fin15Anchored_clause19135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2570 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom2570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17553
  ] at hbad
  tauto

theorem fin15Anchored_clause19136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2570 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom0678 Fin15AnchoredAtom0693
    Fin15AnchoredAtom0778 Fin15AnchoredAtom1569 Fin15AnchoredAtom2570 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17553
  ] at hbad
  tauto

theorem fin15Anchored_clause19137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom0675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0675 Fin15AnchoredAtom2571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06289
  ] at hbad
  tauto

theorem fin15Anchored_clause19138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06289
  ] at hbad
  tauto

theorem fin15Anchored_clause19139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom2571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06289
  ] at hbad
  tauto

theorem fin15Anchored_clause19140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom0779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0779 Fin15AnchoredAtom2571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06289
  ] at hbad
  tauto

theorem fin15Anchored_clause19141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2571 chi ∧
      ¬Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1570 Fin15AnchoredAtom2571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06289
  ] at hbad
  tauto

theorem fin15Anchored_clause19142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2571 chi ∧
      Fin15AnchoredAtom0675 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1570 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0675 Fin15AnchoredAtom0676 Fin15AnchoredAtom0694
    Fin15AnchoredAtom0779 Fin15AnchoredAtom1570 Fin15AnchoredAtom2571 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06289
  ] at hbad
  tauto

theorem fin15Anchored_clause19143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2572 chi ∧
      ¬Fin15AnchoredAtom0695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0695 Fin15AnchoredAtom2572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10385
  ] at hbad
  tauto

theorem fin15Anchored_clause19144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2572 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0780 Fin15AnchoredAtom2572 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10385
  ] at hbad
  tauto

theorem fin15Anchored_clause19145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18577
  ] at hbad
  tauto

theorem fin15Anchored_clause19146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom0696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0696 Fin15AnchoredAtom2573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18577
  ] at hbad
  tauto

theorem fin15Anchored_clause19147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2573 chi ∧
      ¬Fin15AnchoredAtom0781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0781 Fin15AnchoredAtom2573 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18577
  ] at hbad
  tauto

theorem fin15Anchored_clause19148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12433
  ] at hbad
  tauto

theorem fin15Anchored_clause19149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom2574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12433
  ] at hbad
  tauto

theorem fin15Anchored_clause19150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12433
  ] at hbad
  tauto

theorem fin15Anchored_clause19151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12433
  ] at hbad
  tauto

theorem fin15Anchored_clause19152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2574 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom2574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12433
  ] at hbad
  tauto

theorem fin15Anchored_clause19153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2574 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom0677 Fin15AnchoredAtom0697
    Fin15AnchoredAtom0782 Fin15AnchoredAtom1573 Fin15AnchoredAtom2574 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12433
  ] at hbad
  tauto

theorem fin15Anchored_clause19154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20625
  ] at hbad
  tauto

theorem fin15Anchored_clause19155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20625
  ] at hbad
  tauto

theorem fin15Anchored_clause19156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom2575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20625
  ] at hbad
  tauto

theorem fin15Anchored_clause19157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20625
  ] at hbad
  tauto

theorem fin15Anchored_clause19158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2575 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom2575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20625
  ] at hbad
  tauto

theorem fin15Anchored_clause19159 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2575 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom0678 Fin15AnchoredAtom0698
    Fin15AnchoredAtom0783 Fin15AnchoredAtom1574 Fin15AnchoredAtom2575 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20625
  ] at hbad
  tauto

theorem fin15Anchored_clause19160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom2576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24721
  ] at hbad
  tauto

theorem fin15Anchored_clause19161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom2576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24721
  ] at hbad
  tauto

theorem fin15Anchored_clause19162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom2576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24721
  ] at hbad
  tauto

theorem fin15Anchored_clause19163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24721
  ] at hbad
  tauto

theorem fin15Anchored_clause19164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2576 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom2576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24721
  ] at hbad
  tauto

theorem fin15Anchored_clause19165 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2576 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom0678 Fin15AnchoredAtom0699
    Fin15AnchoredAtom0784 Fin15AnchoredAtom1575 Fin15AnchoredAtom2576 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24721
  ] at hbad
  tauto

theorem fin15Anchored_clause19166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom2577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01809
  ] at hbad
  tauto

theorem fin15Anchored_clause19167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom2577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01809
  ] at hbad
  tauto

theorem fin15Anchored_clause19168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01809
  ] at hbad
  tauto

theorem fin15Anchored_clause19169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2577 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom2577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01809
  ] at hbad
  tauto

theorem fin15Anchored_clause19170 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2577 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom0680 Fin15AnchoredAtom0685
    Fin15AnchoredAtom0785 Fin15AnchoredAtom1576 Fin15AnchoredAtom2577 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01809
  ] at hbad
  tauto

theorem fin15Anchored_clause19171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom2579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04881
  ] at hbad
  tauto

theorem fin15Anchored_clause19172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom2579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04881
  ] at hbad
  tauto

theorem fin15Anchored_clause19173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04881
  ] at hbad
  tauto

theorem fin15Anchored_clause19174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom2579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04881
  ] at hbad
  tauto

theorem fin15Anchored_clause19175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2579 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom2579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04881
  ] at hbad
  tauto

theorem fin15Anchored_clause19176 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2579 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom0682 Fin15AnchoredAtom0687
    Fin15AnchoredAtom0787 Fin15AnchoredAtom1578 Fin15AnchoredAtom2579 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04881
  ] at hbad
  tauto

theorem fin15Anchored_clause19177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom2580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08977
  ] at hbad
  tauto

theorem fin15Anchored_clause19178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom2580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08977
  ] at hbad
  tauto

theorem fin15Anchored_clause19179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom2580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08977
  ] at hbad
  tauto

theorem fin15Anchored_clause19180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2580 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom2580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08977
  ] at hbad
  tauto

theorem fin15Anchored_clause19181 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2580 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom0683 Fin15AnchoredAtom0688
    Fin15AnchoredAtom0788 Fin15AnchoredAtom1579 Fin15AnchoredAtom2580 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08977
  ] at hbad
  tauto

theorem fin15Anchored_clause19182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom2581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17169
  ] at hbad
  tauto

theorem fin15Anchored_clause19183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom2581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17169
  ] at hbad
  tauto

theorem fin15Anchored_clause19184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17169
  ] at hbad
  tauto

theorem fin15Anchored_clause19185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0789 Fin15AnchoredAtom2581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17169
  ] at hbad
  tauto

theorem fin15Anchored_clause19186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2581 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1580 Fin15AnchoredAtom2581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17169
  ] at hbad
  tauto

theorem fin15Anchored_clause19187 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2581 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom0684 Fin15AnchoredAtom0689
    Fin15AnchoredAtom0789 Fin15AnchoredAtom1580 Fin15AnchoredAtom2581 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17169
  ] at hbad
  tauto

theorem fin15Anchored_clause19188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom2583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05393
  ] at hbad
  tauto

theorem fin15Anchored_clause19189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom2583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05393
  ] at hbad
  tauto

theorem fin15Anchored_clause19190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05393
  ] at hbad
  tauto

theorem fin15Anchored_clause19191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom2583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05393
  ] at hbad
  tauto

theorem fin15Anchored_clause19192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2583 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom2583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05393
  ] at hbad
  tauto

theorem fin15Anchored_clause19193 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2583 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom0682 Fin15AnchoredAtom0691
    Fin15AnchoredAtom0791 Fin15AnchoredAtom1582 Fin15AnchoredAtom2583 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05393
  ] at hbad
  tauto

theorem fin15Anchored_clause19194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom2584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09489
  ] at hbad
  tauto

theorem fin15Anchored_clause19195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom2584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09489
  ] at hbad
  tauto

theorem fin15Anchored_clause19196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09489
  ] at hbad
  tauto

theorem fin15Anchored_clause19197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09489
  ] at hbad
  tauto

theorem fin15Anchored_clause19198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2584 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom2584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09489
  ] at hbad
  tauto

theorem fin15Anchored_clause19199 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2584 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom0683 Fin15AnchoredAtom0692
    Fin15AnchoredAtom0792 Fin15AnchoredAtom1583 Fin15AnchoredAtom2584 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09489
  ] at hbad
  tauto

end ErdosSzekeres

end
