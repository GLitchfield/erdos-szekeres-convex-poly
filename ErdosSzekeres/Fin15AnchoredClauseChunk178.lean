module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 178. -/

theorem fin15Anchored_clause22784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3397 chi ∧
      ¬Fin15AnchoredAtom1681 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1681 Fin15AnchoredAtom3397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18978
  ] at hbad
  tauto

theorem fin15Anchored_clause22785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom3398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12834
  ] at hbad
  tauto

theorem fin15Anchored_clause22786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom3398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12834
  ] at hbad
  tauto

theorem fin15Anchored_clause22787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom3398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12834
  ] at hbad
  tauto

theorem fin15Anchored_clause22788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12834
  ] at hbad
  tauto

theorem fin15Anchored_clause22789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3398 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom3398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12834
  ] at hbad
  tauto

theorem fin15Anchored_clause22790 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3398 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom1010 Fin15AnchoredAtom1019
    Fin15AnchoredAtom1093 Fin15AnchoredAtom1682 Fin15AnchoredAtom3398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12834
  ] at hbad
  tauto

theorem fin15Anchored_clause22791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom3399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21026
  ] at hbad
  tauto

theorem fin15Anchored_clause22792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom3399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21026
  ] at hbad
  tauto

theorem fin15Anchored_clause22793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom3399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21026
  ] at hbad
  tauto

theorem fin15Anchored_clause22794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21026
  ] at hbad
  tauto

theorem fin15Anchored_clause22795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3399 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom3399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21026
  ] at hbad
  tauto

theorem fin15Anchored_clause22796 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3399 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom1011 Fin15AnchoredAtom1020
    Fin15AnchoredAtom1094 Fin15AnchoredAtom1683 Fin15AnchoredAtom3399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21026
  ] at hbad
  tauto

theorem fin15Anchored_clause22797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom3400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25122
  ] at hbad
  tauto

theorem fin15Anchored_clause22798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom3400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25122
  ] at hbad
  tauto

theorem fin15Anchored_clause22799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom3400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25122
  ] at hbad
  tauto

theorem fin15Anchored_clause22800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom3400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25122
  ] at hbad
  tauto

theorem fin15Anchored_clause22801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3400 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom3400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25122
  ] at hbad
  tauto

theorem fin15Anchored_clause22802 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3400 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom1011 Fin15AnchoredAtom1021
    Fin15AnchoredAtom1095 Fin15AnchoredAtom1684 Fin15AnchoredAtom3400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25122
  ] at hbad
  tauto

theorem fin15Anchored_clause22803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3401 chi ∧
      ¬Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1096 Fin15AnchoredAtom3401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07202
  ] at hbad
  tauto

theorem fin15Anchored_clause22804 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3402 chi ∧
      Fin15AnchoredAtom1012 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1017 chi ∧
      Fin15AnchoredAtom1097 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1012 Fin15AnchoredAtom1014 Fin15AnchoredAtom1017
    Fin15AnchoredAtom1097 Fin15AnchoredAtom1686 Fin15AnchoredAtom3402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11298
  ] at hbad
  tauto

theorem fin15Anchored_clause22805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3403 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom3403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19490
  ] at hbad
  tauto

theorem fin15Anchored_clause22806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom3404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13346
  ] at hbad
  tauto

theorem fin15Anchored_clause22807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom3404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13346
  ] at hbad
  tauto

theorem fin15Anchored_clause22808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom3404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13346
  ] at hbad
  tauto

theorem fin15Anchored_clause22809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13346
  ] at hbad
  tauto

theorem fin15Anchored_clause22810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3404 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom3404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13346
  ] at hbad
  tauto

theorem fin15Anchored_clause22811 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3404 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom1014 Fin15AnchoredAtom1019
    Fin15AnchoredAtom1099 Fin15AnchoredAtom1688 Fin15AnchoredAtom3404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13346
  ] at hbad
  tauto

theorem fin15Anchored_clause22812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom3405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21538
  ] at hbad
  tauto

theorem fin15Anchored_clause22813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom3405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21538
  ] at hbad
  tauto

theorem fin15Anchored_clause22814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom3405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21538
  ] at hbad
  tauto

theorem fin15Anchored_clause22815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21538
  ] at hbad
  tauto

theorem fin15Anchored_clause22816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3405 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom3405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21538
  ] at hbad
  tauto

theorem fin15Anchored_clause22817 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3405 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom1015 Fin15AnchoredAtom1020
    Fin15AnchoredAtom1100 Fin15AnchoredAtom1689 Fin15AnchoredAtom3405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21538
  ] at hbad
  tauto

theorem fin15Anchored_clause22818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom3406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25634
  ] at hbad
  tauto

theorem fin15Anchored_clause22819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom3406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25634
  ] at hbad
  tauto

theorem fin15Anchored_clause22820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom3406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25634
  ] at hbad
  tauto

theorem fin15Anchored_clause22821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25634
  ] at hbad
  tauto

theorem fin15Anchored_clause22822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3406 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom3406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25634
  ] at hbad
  tauto

theorem fin15Anchored_clause22823 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3406 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom1015 Fin15AnchoredAtom1021
    Fin15AnchoredAtom1101 Fin15AnchoredAtom1690 Fin15AnchoredAtom3406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25634
  ] at hbad
  tauto

theorem fin15Anchored_clause22824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3407 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom3407 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14370
  ] at hbad
  tauto

theorem fin15Anchored_clause22825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3408 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom3408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22562
  ] at hbad
  tauto

theorem fin15Anchored_clause22826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom3410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28706
  ] at hbad
  tauto

theorem fin15Anchored_clause22827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom3410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28706
  ] at hbad
  tauto

theorem fin15Anchored_clause22828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom3410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28706
  ] at hbad
  tauto

theorem fin15Anchored_clause22829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28706
  ] at hbad
  tauto

theorem fin15Anchored_clause22830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3410 chi ∧
      ¬Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1694 Fin15AnchoredAtom3410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28706
  ] at hbad
  tauto

theorem fin15Anchored_clause22831 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3410 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom1020 Fin15AnchoredAtom1021
    Fin15AnchoredAtom1105 Fin15AnchoredAtom1694 Fin15AnchoredAtom3410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28706
  ] at hbad
  tauto

theorem fin15Anchored_clause22832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom3411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00962
  ] at hbad
  tauto

theorem fin15Anchored_clause22833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom3411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00962
  ] at hbad
  tauto

theorem fin15Anchored_clause22834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom3411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00962
  ] at hbad
  tauto

theorem fin15Anchored_clause22835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom3411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00962
  ] at hbad
  tauto

theorem fin15Anchored_clause22836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3411 chi ∧
      ¬Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1695 Fin15AnchoredAtom3411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00962
  ] at hbad
  tauto

theorem fin15Anchored_clause22837 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3411 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom1023 Fin15AnchoredAtom1029
    Fin15AnchoredAtom1050 Fin15AnchoredAtom1695 Fin15AnchoredAtom3411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00962
  ] at hbad
  tauto

theorem fin15Anchored_clause22838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom3412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01474
  ] at hbad
  tauto

theorem fin15Anchored_clause22839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom3412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01474
  ] at hbad
  tauto

theorem fin15Anchored_clause22840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom3412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01474
  ] at hbad
  tauto

theorem fin15Anchored_clause22841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom3412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01474
  ] at hbad
  tauto

theorem fin15Anchored_clause22842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3412 chi ∧
      ¬Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1696 Fin15AnchoredAtom3412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01474
  ] at hbad
  tauto

theorem fin15Anchored_clause22843 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3412 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1696 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom1024 Fin15AnchoredAtom1030
    Fin15AnchoredAtom1051 Fin15AnchoredAtom1696 Fin15AnchoredAtom3412 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01474
  ] at hbad
  tauto

theorem fin15Anchored_clause22844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom3414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04546
  ] at hbad
  tauto

theorem fin15Anchored_clause22845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom3414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04546
  ] at hbad
  tauto

theorem fin15Anchored_clause22846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom3414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04546
  ] at hbad
  tauto

theorem fin15Anchored_clause22847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3414 chi ∧
      ¬Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1698 Fin15AnchoredAtom3414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04546
  ] at hbad
  tauto

theorem fin15Anchored_clause22848 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3414 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom1026 Fin15AnchoredAtom1032
    Fin15AnchoredAtom1053 Fin15AnchoredAtom1698 Fin15AnchoredAtom3414 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04546
  ] at hbad
  tauto

theorem fin15Anchored_clause22849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom3415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08642
  ] at hbad
  tauto

theorem fin15Anchored_clause22850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom3415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08642
  ] at hbad
  tauto

theorem fin15Anchored_clause22851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom3415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08642
  ] at hbad
  tauto

theorem fin15Anchored_clause22852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom3415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08642
  ] at hbad
  tauto

theorem fin15Anchored_clause22853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3415 chi ∧
      ¬Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1699 Fin15AnchoredAtom3415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08642
  ] at hbad
  tauto

theorem fin15Anchored_clause22854 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3415 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom1027 Fin15AnchoredAtom1033
    Fin15AnchoredAtom1054 Fin15AnchoredAtom1699 Fin15AnchoredAtom3415 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08642
  ] at hbad
  tauto

theorem fin15Anchored_clause22855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom1022 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom3416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16834
  ] at hbad
  tauto

theorem fin15Anchored_clause22856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom3416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16834
  ] at hbad
  tauto

theorem fin15Anchored_clause22857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1034 Fin15AnchoredAtom3416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16834
  ] at hbad
  tauto

theorem fin15Anchored_clause22858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3416 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1055 Fin15AnchoredAtom3416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16834
  ] at hbad
  tauto

theorem fin15Anchored_clause22859 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3416 chi ∧
      Fin15AnchoredAtom1022 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1700 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1022 Fin15AnchoredAtom1028 Fin15AnchoredAtom1034
    Fin15AnchoredAtom1055 Fin15AnchoredAtom1700 Fin15AnchoredAtom3416 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16834
  ] at hbad
  tauto

theorem fin15Anchored_clause22860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom3417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01730
  ] at hbad
  tauto

theorem fin15Anchored_clause22861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom3417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01730
  ] at hbad
  tauto

theorem fin15Anchored_clause22862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom3417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01730
  ] at hbad
  tauto

theorem fin15Anchored_clause22863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom3417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01730
  ] at hbad
  tauto

theorem fin15Anchored_clause22864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3417 chi ∧
      ¬Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1701 Fin15AnchoredAtom3417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01730
  ] at hbad
  tauto

theorem fin15Anchored_clause22865 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3417 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1701 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom1024 Fin15AnchoredAtom1035
    Fin15AnchoredAtom1056 Fin15AnchoredAtom1701 Fin15AnchoredAtom3417 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01730
  ] at hbad
  tauto

theorem fin15Anchored_clause22866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3418 chi ∧
      ¬Fin15AnchoredAtom1025 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1025 Fin15AnchoredAtom3418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02754
  ] at hbad
  tauto

theorem fin15Anchored_clause22867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3418 chi ∧
      ¬Fin15AnchoredAtom1057 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1057 Fin15AnchoredAtom3418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02754
  ] at hbad
  tauto

theorem fin15Anchored_clause22868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3418 chi ∧
      ¬Fin15AnchoredAtom1702 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1702 Fin15AnchoredAtom3418 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02754
  ] at hbad
  tauto

theorem fin15Anchored_clause22869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom3419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04802
  ] at hbad
  tauto

theorem fin15Anchored_clause22870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom3419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04802
  ] at hbad
  tauto

theorem fin15Anchored_clause22871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom3419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04802
  ] at hbad
  tauto

theorem fin15Anchored_clause22872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom3419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04802
  ] at hbad
  tauto

theorem fin15Anchored_clause22873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3419 chi ∧
      ¬Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1703 Fin15AnchoredAtom3419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04802
  ] at hbad
  tauto

theorem fin15Anchored_clause22874 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3419 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1703 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom1026 Fin15AnchoredAtom1037
    Fin15AnchoredAtom1058 Fin15AnchoredAtom1703 Fin15AnchoredAtom3419 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04802
  ] at hbad
  tauto

theorem fin15Anchored_clause22875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom3420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08898
  ] at hbad
  tauto

theorem fin15Anchored_clause22876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom3420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08898
  ] at hbad
  tauto

theorem fin15Anchored_clause22877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom3420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08898
  ] at hbad
  tauto

theorem fin15Anchored_clause22878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom3420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08898
  ] at hbad
  tauto

theorem fin15Anchored_clause22879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3420 chi ∧
      ¬Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1704 Fin15AnchoredAtom3420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08898
  ] at hbad
  tauto

theorem fin15Anchored_clause22880 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3420 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1704 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom1027 Fin15AnchoredAtom1038
    Fin15AnchoredAtom1059 Fin15AnchoredAtom1704 Fin15AnchoredAtom3420 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08898
  ] at hbad
  tauto

theorem fin15Anchored_clause22881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1023 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom3421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17090
  ] at hbad
  tauto

theorem fin15Anchored_clause22882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom3421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17090
  ] at hbad
  tauto

theorem fin15Anchored_clause22883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom3421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17090
  ] at hbad
  tauto

theorem fin15Anchored_clause22884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom3421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17090
  ] at hbad
  tauto

theorem fin15Anchored_clause22885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3421 chi ∧
      ¬Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1705 Fin15AnchoredAtom3421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17090
  ] at hbad
  tauto

theorem fin15Anchored_clause22886 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3421 chi ∧
      Fin15AnchoredAtom1023 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1705 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1023 Fin15AnchoredAtom1028 Fin15AnchoredAtom1039
    Fin15AnchoredAtom1060 Fin15AnchoredAtom1705 Fin15AnchoredAtom3421 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17090
  ] at hbad
  tauto

theorem fin15Anchored_clause22887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3422 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom3422 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03266
  ] at hbad
  tauto

theorem fin15Anchored_clause22888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3422 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1040 Fin15AnchoredAtom3422 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03266
  ] at hbad
  tauto

theorem fin15Anchored_clause22889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3422 chi ∧
      ¬Fin15AnchoredAtom1706 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1706 Fin15AnchoredAtom3422 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03266
  ] at hbad
  tauto

theorem fin15Anchored_clause22890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom3423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05314
  ] at hbad
  tauto

theorem fin15Anchored_clause22891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom3423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05314
  ] at hbad
  tauto

theorem fin15Anchored_clause22892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom3423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05314
  ] at hbad
  tauto

theorem fin15Anchored_clause22893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom3423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05314
  ] at hbad
  tauto

theorem fin15Anchored_clause22894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3423 chi ∧
      ¬Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1707 Fin15AnchoredAtom3423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05314
  ] at hbad
  tauto

theorem fin15Anchored_clause22895 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3423 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1707 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom1026 Fin15AnchoredAtom1041
    Fin15AnchoredAtom1062 Fin15AnchoredAtom1707 Fin15AnchoredAtom3423 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05314
  ] at hbad
  tauto

theorem fin15Anchored_clause22896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom3424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09410
  ] at hbad
  tauto

theorem fin15Anchored_clause22897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom3424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09410
  ] at hbad
  tauto

theorem fin15Anchored_clause22898 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom3424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09410
  ] at hbad
  tauto

theorem fin15Anchored_clause22899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom3424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09410
  ] at hbad
  tauto

theorem fin15Anchored_clause22900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3424 chi ∧
      ¬Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1708 Fin15AnchoredAtom3424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09410
  ] at hbad
  tauto

theorem fin15Anchored_clause22901 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3424 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1708 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom1027 Fin15AnchoredAtom1042
    Fin15AnchoredAtom1063 Fin15AnchoredAtom1708 Fin15AnchoredAtom3424 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09410
  ] at hbad
  tauto

theorem fin15Anchored_clause22902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1024 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom3425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17602
  ] at hbad
  tauto

theorem fin15Anchored_clause22903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom3425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17602
  ] at hbad
  tauto

theorem fin15Anchored_clause22904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom3425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17602
  ] at hbad
  tauto

theorem fin15Anchored_clause22905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17602
  ] at hbad
  tauto

theorem fin15Anchored_clause22906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3425 chi ∧
      ¬Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1709 Fin15AnchoredAtom3425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17602
  ] at hbad
  tauto

theorem fin15Anchored_clause22907 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3425 chi ∧
      Fin15AnchoredAtom1024 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1709 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1024 Fin15AnchoredAtom1028 Fin15AnchoredAtom1043
    Fin15AnchoredAtom1064 Fin15AnchoredAtom1709 Fin15AnchoredAtom3425 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17602
  ] at hbad
  tauto

theorem fin15Anchored_clause22908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3426 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom3426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06338
  ] at hbad
  tauto

theorem fin15Anchored_clause22909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3426 chi ∧
      ¬Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1065 Fin15AnchoredAtom3426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06338
  ] at hbad
  tauto

theorem fin15Anchored_clause22910 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3426 chi ∧
      ¬Fin15AnchoredAtom1710 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1710 Fin15AnchoredAtom3426 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06338
  ] at hbad
  tauto

theorem fin15Anchored_clause22911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3428 chi ∧
      ¬Fin15AnchoredAtom1712 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1712 Fin15AnchoredAtom3428 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18626
  ] at hbad
  tauto

end ErdosSzekeres

end
