module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 170. -/

theorem fin15Anchored_clause21760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom3164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09354
  ] at hbad
  tauto

theorem fin15Anchored_clause21761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom3164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09354
  ] at hbad
  tauto

theorem fin15Anchored_clause21762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom3164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09354
  ] at hbad
  tauto

theorem fin15Anchored_clause21763 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3164 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom0918 Fin15AnchoredAtom0933
    Fin15AnchoredAtom1063 Fin15AnchoredAtom1448 Fin15AnchoredAtom3164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09354
  ] at hbad
  tauto

theorem fin15Anchored_clause21764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom3165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17546
  ] at hbad
  tauto

theorem fin15Anchored_clause21765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom3165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17546
  ] at hbad
  tauto

theorem fin15Anchored_clause21766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom3165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17546
  ] at hbad
  tauto

theorem fin15Anchored_clause21767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17546
  ] at hbad
  tauto

theorem fin15Anchored_clause21768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3165 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom3165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17546
  ] at hbad
  tauto

theorem fin15Anchored_clause21769 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3165 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom0919 Fin15AnchoredAtom0934
    Fin15AnchoredAtom1064 Fin15AnchoredAtom1449 Fin15AnchoredAtom3165 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17546
  ] at hbad
  tauto

theorem fin15Anchored_clause21770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom3166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06282
  ] at hbad
  tauto

theorem fin15Anchored_clause21771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0935 Fin15AnchoredAtom3166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06282
  ] at hbad
  tauto

theorem fin15Anchored_clause21772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1065 Fin15AnchoredAtom3166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06282
  ] at hbad
  tauto

theorem fin15Anchored_clause21773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3166 chi ∧
      ¬Fin15AnchoredAtom1450 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1450 Fin15AnchoredAtom3166 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06282
  ] at hbad
  tauto

theorem fin15Anchored_clause21774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3167 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom3167 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10378
  ] at hbad
  tauto

theorem fin15Anchored_clause21775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3168 chi ∧
      ¬Fin15AnchoredAtom0937 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0937 Fin15AnchoredAtom3168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18570
  ] at hbad
  tauto

theorem fin15Anchored_clause21776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3168 chi ∧
      ¬Fin15AnchoredAtom1067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1067 Fin15AnchoredAtom3168 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18570
  ] at hbad
  tauto

theorem fin15Anchored_clause21777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom3169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12426
  ] at hbad
  tauto

theorem fin15Anchored_clause21778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom3169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12426
  ] at hbad
  tauto

theorem fin15Anchored_clause21779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom3169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12426
  ] at hbad
  tauto

theorem fin15Anchored_clause21780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12426
  ] at hbad
  tauto

theorem fin15Anchored_clause21781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3169 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom3169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12426
  ] at hbad
  tauto

theorem fin15Anchored_clause21782 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3169 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom0918 Fin15AnchoredAtom0938
    Fin15AnchoredAtom1068 Fin15AnchoredAtom1453 Fin15AnchoredAtom3169 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12426
  ] at hbad
  tauto

theorem fin15Anchored_clause21783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom3170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20618
  ] at hbad
  tauto

theorem fin15Anchored_clause21784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom3170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20618
  ] at hbad
  tauto

theorem fin15Anchored_clause21785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom3170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20618
  ] at hbad
  tauto

theorem fin15Anchored_clause21786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20618
  ] at hbad
  tauto

theorem fin15Anchored_clause21787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3170 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom3170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20618
  ] at hbad
  tauto

theorem fin15Anchored_clause21788 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3170 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom0919 Fin15AnchoredAtom0939
    Fin15AnchoredAtom1069 Fin15AnchoredAtom1454 Fin15AnchoredAtom3170 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20618
  ] at hbad
  tauto

theorem fin15Anchored_clause21789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom3171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24714
  ] at hbad
  tauto

theorem fin15Anchored_clause21790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom3171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24714
  ] at hbad
  tauto

theorem fin15Anchored_clause21791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom3171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24714
  ] at hbad
  tauto

theorem fin15Anchored_clause21792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24714
  ] at hbad
  tauto

theorem fin15Anchored_clause21793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3171 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom3171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24714
  ] at hbad
  tauto

theorem fin15Anchored_clause21794 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3171 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom0919 Fin15AnchoredAtom0940
    Fin15AnchoredAtom1070 Fin15AnchoredAtom1455 Fin15AnchoredAtom3171 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24714
  ] at hbad
  tauto

theorem fin15Anchored_clause21795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom3172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01802
  ] at hbad
  tauto

theorem fin15Anchored_clause21796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom3172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01802
  ] at hbad
  tauto

theorem fin15Anchored_clause21797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom3172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01802
  ] at hbad
  tauto

theorem fin15Anchored_clause21798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom3172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01802
  ] at hbad
  tauto

theorem fin15Anchored_clause21799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3172 chi ∧
      ¬Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1456 Fin15AnchoredAtom3172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01802
  ] at hbad
  tauto

theorem fin15Anchored_clause21800 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3172 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom0921 Fin15AnchoredAtom0926
    Fin15AnchoredAtom1071 Fin15AnchoredAtom1456 Fin15AnchoredAtom3172 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01802
  ] at hbad
  tauto

theorem fin15Anchored_clause21801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom3174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04874
  ] at hbad
  tauto

theorem fin15Anchored_clause21802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0923 Fin15AnchoredAtom3174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04874
  ] at hbad
  tauto

theorem fin15Anchored_clause21803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom3174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04874
  ] at hbad
  tauto

theorem fin15Anchored_clause21804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom3174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04874
  ] at hbad
  tauto

theorem fin15Anchored_clause21805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3174 chi ∧
      ¬Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1458 Fin15AnchoredAtom3174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04874
  ] at hbad
  tauto

theorem fin15Anchored_clause21806 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3174 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1458 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom0923 Fin15AnchoredAtom0928
    Fin15AnchoredAtom1073 Fin15AnchoredAtom1458 Fin15AnchoredAtom3174 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04874
  ] at hbad
  tauto

theorem fin15Anchored_clause21807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom3175 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08970
  ] at hbad
  tauto

theorem fin15Anchored_clause21808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom3175 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08970
  ] at hbad
  tauto

theorem fin15Anchored_clause21809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom3175 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08970
  ] at hbad
  tauto

theorem fin15Anchored_clause21810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1074 Fin15AnchoredAtom3175 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08970
  ] at hbad
  tauto

theorem fin15Anchored_clause21811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3175 chi ∧
      ¬Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1459 Fin15AnchoredAtom3175 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08970
  ] at hbad
  tauto

theorem fin15Anchored_clause21812 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3175 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1459 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom0924 Fin15AnchoredAtom0929
    Fin15AnchoredAtom1074 Fin15AnchoredAtom1459 Fin15AnchoredAtom3175 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08970
  ] at hbad
  tauto

theorem fin15Anchored_clause21813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom3176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17162
  ] at hbad
  tauto

theorem fin15Anchored_clause21814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom0925 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0925 Fin15AnchoredAtom3176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17162
  ] at hbad
  tauto

theorem fin15Anchored_clause21815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom3176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17162
  ] at hbad
  tauto

theorem fin15Anchored_clause21816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1075 Fin15AnchoredAtom3176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17162
  ] at hbad
  tauto

theorem fin15Anchored_clause21817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3176 chi ∧
      ¬Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1460 Fin15AnchoredAtom3176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17162
  ] at hbad
  tauto

theorem fin15Anchored_clause21818 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3176 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1075 chi ∧
      Fin15AnchoredAtom1460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom0925 Fin15AnchoredAtom0930
    Fin15AnchoredAtom1075 Fin15AnchoredAtom1460 Fin15AnchoredAtom3176 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17162
  ] at hbad
  tauto

theorem fin15Anchored_clause21819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom3178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05386
  ] at hbad
  tauto

theorem fin15Anchored_clause21820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0923 Fin15AnchoredAtom3178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05386
  ] at hbad
  tauto

theorem fin15Anchored_clause21821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom3178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05386
  ] at hbad
  tauto

theorem fin15Anchored_clause21822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1077 Fin15AnchoredAtom3178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05386
  ] at hbad
  tauto

theorem fin15Anchored_clause21823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3178 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom3178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05386
  ] at hbad
  tauto

theorem fin15Anchored_clause21824 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3178 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom0923 Fin15AnchoredAtom0932
    Fin15AnchoredAtom1077 Fin15AnchoredAtom1462 Fin15AnchoredAtom3178 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05386
  ] at hbad
  tauto

theorem fin15Anchored_clause21825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom3179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09482
  ] at hbad
  tauto

theorem fin15Anchored_clause21826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom3179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09482
  ] at hbad
  tauto

theorem fin15Anchored_clause21827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom3179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09482
  ] at hbad
  tauto

theorem fin15Anchored_clause21828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom3179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09482
  ] at hbad
  tauto

theorem fin15Anchored_clause21829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3179 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom3179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09482
  ] at hbad
  tauto

theorem fin15Anchored_clause21830 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3179 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom0924 Fin15AnchoredAtom0933
    Fin15AnchoredAtom1078 Fin15AnchoredAtom1463 Fin15AnchoredAtom3179 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09482
  ] at hbad
  tauto

theorem fin15Anchored_clause21831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom0921 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom3180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17674
  ] at hbad
  tauto

theorem fin15Anchored_clause21832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom3180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17674
  ] at hbad
  tauto

theorem fin15Anchored_clause21833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1079 Fin15AnchoredAtom3180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17674
  ] at hbad
  tauto

theorem fin15Anchored_clause21834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3180 chi ∧
      ¬Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1464 Fin15AnchoredAtom3180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17674
  ] at hbad
  tauto

theorem fin15Anchored_clause21835 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3180 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1079 chi ∧
      Fin15AnchoredAtom1464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0921 Fin15AnchoredAtom0925 Fin15AnchoredAtom0934
    Fin15AnchoredAtom1079 Fin15AnchoredAtom1464 Fin15AnchoredAtom3180 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17674
  ] at hbad
  tauto

theorem fin15Anchored_clause21836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0923 Fin15AnchoredAtom3184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12554
  ] at hbad
  tauto

theorem fin15Anchored_clause21837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom3184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12554
  ] at hbad
  tauto

theorem fin15Anchored_clause21838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom3184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12554
  ] at hbad
  tauto

theorem fin15Anchored_clause21839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1083 Fin15AnchoredAtom3184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12554
  ] at hbad
  tauto

theorem fin15Anchored_clause21840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3184 chi ∧
      ¬Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1468 Fin15AnchoredAtom3184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12554
  ] at hbad
  tauto

theorem fin15Anchored_clause21841 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3184 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0923 Fin15AnchoredAtom0924 Fin15AnchoredAtom0938
    Fin15AnchoredAtom1083 Fin15AnchoredAtom1468 Fin15AnchoredAtom3184 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12554
  ] at hbad
  tauto

theorem fin15Anchored_clause21842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom0923 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0923 Fin15AnchoredAtom3185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20746
  ] at hbad
  tauto

theorem fin15Anchored_clause21843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom3185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20746
  ] at hbad
  tauto

theorem fin15Anchored_clause21844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3185 chi ∧
      ¬Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1084 Fin15AnchoredAtom3185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20746
  ] at hbad
  tauto

theorem fin15Anchored_clause21845 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3185 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0923 Fin15AnchoredAtom0925 Fin15AnchoredAtom0939
    Fin15AnchoredAtom1084 Fin15AnchoredAtom1469 Fin15AnchoredAtom3185 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20746
  ] at hbad
  tauto

theorem fin15Anchored_clause21846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom3186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24842
  ] at hbad
  tauto

theorem fin15Anchored_clause21847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom3186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24842
  ] at hbad
  tauto

theorem fin15Anchored_clause21848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1085 Fin15AnchoredAtom3186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24842
  ] at hbad
  tauto

theorem fin15Anchored_clause21849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3186 chi ∧
      ¬Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1470 Fin15AnchoredAtom3186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24842
  ] at hbad
  tauto

theorem fin15Anchored_clause21850 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3186 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom0925 Fin15AnchoredAtom0940
    Fin15AnchoredAtom1085 Fin15AnchoredAtom1470 Fin15AnchoredAtom3186 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24842
  ] at hbad
  tauto

theorem fin15Anchored_clause21851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom3187 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03594
  ] at hbad
  tauto

theorem fin15Anchored_clause21852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom1086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1086 Fin15AnchoredAtom3187 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03594
  ] at hbad
  tauto

theorem fin15Anchored_clause21853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3187 chi ∧
      ¬Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1471 Fin15AnchoredAtom3187 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03594
  ] at hbad
  tauto

theorem fin15Anchored_clause21854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom3188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05642
  ] at hbad
  tauto

theorem fin15Anchored_clause21855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom3188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05642
  ] at hbad
  tauto

theorem fin15Anchored_clause21856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom3188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05642
  ] at hbad
  tauto

theorem fin15Anchored_clause21857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05642
  ] at hbad
  tauto

theorem fin15Anchored_clause21858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3188 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom3188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05642
  ] at hbad
  tauto

theorem fin15Anchored_clause21859 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3188 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom0928 Fin15AnchoredAtom0932
    Fin15AnchoredAtom1087 Fin15AnchoredAtom1472 Fin15AnchoredAtom3188 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05642
  ] at hbad
  tauto

theorem fin15Anchored_clause21860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom3189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09738
  ] at hbad
  tauto

theorem fin15Anchored_clause21861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom3189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09738
  ] at hbad
  tauto

theorem fin15Anchored_clause21862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom3189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09738
  ] at hbad
  tauto

theorem fin15Anchored_clause21863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09738
  ] at hbad
  tauto

theorem fin15Anchored_clause21864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3189 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom3189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09738
  ] at hbad
  tauto

theorem fin15Anchored_clause21865 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3189 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom0929 Fin15AnchoredAtom0933
    Fin15AnchoredAtom1088 Fin15AnchoredAtom1473 Fin15AnchoredAtom3189 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09738
  ] at hbad
  tauto

theorem fin15Anchored_clause21866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom3190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17930
  ] at hbad
  tauto

theorem fin15Anchored_clause21867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom3190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17930
  ] at hbad
  tauto

theorem fin15Anchored_clause21868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom3190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17930
  ] at hbad
  tauto

theorem fin15Anchored_clause21869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom3190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17930
  ] at hbad
  tauto

theorem fin15Anchored_clause21870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3190 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom3190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17930
  ] at hbad
  tauto

theorem fin15Anchored_clause21871 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3190 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom0930 Fin15AnchoredAtom0934
    Fin15AnchoredAtom1089 Fin15AnchoredAtom1474 Fin15AnchoredAtom3190 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17930
  ] at hbad
  tauto

theorem fin15Anchored_clause21872 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom3191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06666
  ] at hbad
  tauto

theorem fin15Anchored_clause21873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom0935 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0935 Fin15AnchoredAtom3191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06666
  ] at hbad
  tauto

theorem fin15Anchored_clause21874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1090 Fin15AnchoredAtom3191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06666
  ] at hbad
  tauto

theorem fin15Anchored_clause21875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3191 chi ∧
      ¬Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1475 Fin15AnchoredAtom3191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06666
  ] at hbad
  tauto

theorem fin15Anchored_clause21876 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3191 chi ∧
      Fin15AnchoredAtom0927 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0935 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0927 Fin15AnchoredAtom0928 Fin15AnchoredAtom0935
    Fin15AnchoredAtom1090 Fin15AnchoredAtom1475 Fin15AnchoredAtom3191 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06666
  ] at hbad
  tauto

theorem fin15Anchored_clause21877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3192 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom3192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10762
  ] at hbad
  tauto

theorem fin15Anchored_clause21878 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3192 chi ∧
      Fin15AnchoredAtom0927 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0936 chi ∧
      Fin15AnchoredAtom1091 chi ∧
      Fin15AnchoredAtom1476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0927 Fin15AnchoredAtom0929 Fin15AnchoredAtom0936
    Fin15AnchoredAtom1091 Fin15AnchoredAtom1476 Fin15AnchoredAtom3192 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10762
  ] at hbad
  tauto

theorem fin15Anchored_clause21879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3193 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom3193 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18954
  ] at hbad
  tauto

theorem fin15Anchored_clause21880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom3194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12810
  ] at hbad
  tauto

theorem fin15Anchored_clause21881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom3194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12810
  ] at hbad
  tauto

theorem fin15Anchored_clause21882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom3194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12810
  ] at hbad
  tauto

theorem fin15Anchored_clause21883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12810
  ] at hbad
  tauto

theorem fin15Anchored_clause21884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3194 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom3194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12810
  ] at hbad
  tauto

theorem fin15Anchored_clause21885 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3194 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom0929 Fin15AnchoredAtom0938
    Fin15AnchoredAtom1093 Fin15AnchoredAtom1478 Fin15AnchoredAtom3194 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12810
  ] at hbad
  tauto

theorem fin15Anchored_clause21886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom3195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21002
  ] at hbad
  tauto

theorem fin15Anchored_clause21887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3195 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom3195 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21002
  ] at hbad
  tauto

end ErdosSzekeres

end
