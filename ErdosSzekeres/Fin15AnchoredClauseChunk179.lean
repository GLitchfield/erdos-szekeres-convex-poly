module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 179. -/

theorem fin15Anchored_clause22912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom3429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12482
  ] at hbad
  tauto

theorem fin15Anchored_clause22913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom3429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12482
  ] at hbad
  tauto

theorem fin15Anchored_clause22914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom3429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12482
  ] at hbad
  tauto

theorem fin15Anchored_clause22915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12482
  ] at hbad
  tauto

theorem fin15Anchored_clause22916 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3429 chi ∧
      ¬Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1713 Fin15AnchoredAtom3429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12482
  ] at hbad
  tauto

theorem fin15Anchored_clause22917 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3429 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1713 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom1027 Fin15AnchoredAtom1047
    Fin15AnchoredAtom1068 Fin15AnchoredAtom1713 Fin15AnchoredAtom3429 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12482
  ] at hbad
  tauto

theorem fin15Anchored_clause22918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1026 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom3430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20674
  ] at hbad
  tauto

theorem fin15Anchored_clause22919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom3430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20674
  ] at hbad
  tauto

theorem fin15Anchored_clause22920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom3430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20674
  ] at hbad
  tauto

theorem fin15Anchored_clause22921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20674
  ] at hbad
  tauto

theorem fin15Anchored_clause22922 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3430 chi ∧
      ¬Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1714 Fin15AnchoredAtom3430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20674
  ] at hbad
  tauto

theorem fin15Anchored_clause22923 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3430 chi ∧
      Fin15AnchoredAtom1026 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1714 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1026 Fin15AnchoredAtom1028 Fin15AnchoredAtom1048
    Fin15AnchoredAtom1069 Fin15AnchoredAtom1714 Fin15AnchoredAtom3430 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20674
  ] at hbad
  tauto

theorem fin15Anchored_clause22924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1027 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom3431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24770
  ] at hbad
  tauto

theorem fin15Anchored_clause22925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1028 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1028 Fin15AnchoredAtom3431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24770
  ] at hbad
  tauto

theorem fin15Anchored_clause22926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom3431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24770
  ] at hbad
  tauto

theorem fin15Anchored_clause22927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24770
  ] at hbad
  tauto

theorem fin15Anchored_clause22928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3431 chi ∧
      ¬Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1715 Fin15AnchoredAtom3431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24770
  ] at hbad
  tauto

theorem fin15Anchored_clause22929 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3431 chi ∧
      Fin15AnchoredAtom1027 chi ∧
      Fin15AnchoredAtom1028 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1027 Fin15AnchoredAtom1028 Fin15AnchoredAtom1049
    Fin15AnchoredAtom1070 Fin15AnchoredAtom1715 Fin15AnchoredAtom3431 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24770
  ] at hbad
  tauto

theorem fin15Anchored_clause22930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom3432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01858
  ] at hbad
  tauto

theorem fin15Anchored_clause22931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom3432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01858
  ] at hbad
  tauto

theorem fin15Anchored_clause22932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom3432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01858
  ] at hbad
  tauto

theorem fin15Anchored_clause22933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom3432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01858
  ] at hbad
  tauto

theorem fin15Anchored_clause22934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3432 chi ∧
      ¬Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1716 Fin15AnchoredAtom3432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01858
  ] at hbad
  tauto

theorem fin15Anchored_clause22935 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3432 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom1030 Fin15AnchoredAtom1035
    Fin15AnchoredAtom1071 Fin15AnchoredAtom1716 Fin15AnchoredAtom3432 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01858
  ] at hbad
  tauto

theorem fin15Anchored_clause22936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom3434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04930
  ] at hbad
  tauto

theorem fin15Anchored_clause22937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom3434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04930
  ] at hbad
  tauto

theorem fin15Anchored_clause22938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom3434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04930
  ] at hbad
  tauto

theorem fin15Anchored_clause22939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom3434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04930
  ] at hbad
  tauto

theorem fin15Anchored_clause22940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3434 chi ∧
      ¬Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1718 Fin15AnchoredAtom3434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04930
  ] at hbad
  tauto

theorem fin15Anchored_clause22941 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3434 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom1032 Fin15AnchoredAtom1037
    Fin15AnchoredAtom1073 Fin15AnchoredAtom1718 Fin15AnchoredAtom3434 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04930
  ] at hbad
  tauto

theorem fin15Anchored_clause22942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom3435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09026
  ] at hbad
  tauto

theorem fin15Anchored_clause22943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom3435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09026
  ] at hbad
  tauto

theorem fin15Anchored_clause22944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom3435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09026
  ] at hbad
  tauto

theorem fin15Anchored_clause22945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1074 Fin15AnchoredAtom3435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09026
  ] at hbad
  tauto

theorem fin15Anchored_clause22946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3435 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom3435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09026
  ] at hbad
  tauto

theorem fin15Anchored_clause22947 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3435 chi ∧
      Fin15AnchoredAtom1029 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom1033 Fin15AnchoredAtom1038
    Fin15AnchoredAtom1074 Fin15AnchoredAtom1719 Fin15AnchoredAtom3435 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09026
  ] at hbad
  tauto

theorem fin15Anchored_clause22948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom1029 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1029 Fin15AnchoredAtom3436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17218
  ] at hbad
  tauto

theorem fin15Anchored_clause22949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1034 Fin15AnchoredAtom3436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17218
  ] at hbad
  tauto

theorem fin15Anchored_clause22950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom3436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17218
  ] at hbad
  tauto

theorem fin15Anchored_clause22951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3436 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1720 Fin15AnchoredAtom3436 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17218
  ] at hbad
  tauto

theorem fin15Anchored_clause22952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom3438 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05442
  ] at hbad
  tauto

theorem fin15Anchored_clause22953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom3438 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05442
  ] at hbad
  tauto

theorem fin15Anchored_clause22954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom3438 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05442
  ] at hbad
  tauto

theorem fin15Anchored_clause22955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3438 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom3438 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05442
  ] at hbad
  tauto

theorem fin15Anchored_clause22956 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3438 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom1032 Fin15AnchoredAtom1041
    Fin15AnchoredAtom1077 Fin15AnchoredAtom1722 Fin15AnchoredAtom3438 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05442
  ] at hbad
  tauto

theorem fin15Anchored_clause22957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom3439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09538
  ] at hbad
  tauto

theorem fin15Anchored_clause22958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom3439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09538
  ] at hbad
  tauto

theorem fin15Anchored_clause22959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom3439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09538
  ] at hbad
  tauto

theorem fin15Anchored_clause22960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom3439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09538
  ] at hbad
  tauto

theorem fin15Anchored_clause22961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3439 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1723 Fin15AnchoredAtom3439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09538
  ] at hbad
  tauto

theorem fin15Anchored_clause22962 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3439 chi ∧
      Fin15AnchoredAtom1030 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom1033 Fin15AnchoredAtom1042
    Fin15AnchoredAtom1078 Fin15AnchoredAtom1723 Fin15AnchoredAtom3439 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09538
  ] at hbad
  tauto

theorem fin15Anchored_clause22963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1030 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1030 Fin15AnchoredAtom3440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17730
  ] at hbad
  tauto

theorem fin15Anchored_clause22964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1034 Fin15AnchoredAtom3440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17730
  ] at hbad
  tauto

theorem fin15Anchored_clause22965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom3440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17730
  ] at hbad
  tauto

theorem fin15Anchored_clause22966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1079 Fin15AnchoredAtom3440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17730
  ] at hbad
  tauto

theorem fin15Anchored_clause22967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3440 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1724 Fin15AnchoredAtom3440 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17730
  ] at hbad
  tauto

theorem fin15Anchored_clause22968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom3444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12610
  ] at hbad
  tauto

theorem fin15Anchored_clause22969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom3444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12610
  ] at hbad
  tauto

theorem fin15Anchored_clause22970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom3444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12610
  ] at hbad
  tauto

theorem fin15Anchored_clause22971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1083 Fin15AnchoredAtom3444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12610
  ] at hbad
  tauto

theorem fin15Anchored_clause22972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3444 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom3444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12610
  ] at hbad
  tauto

theorem fin15Anchored_clause22973 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3444 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom1033 Fin15AnchoredAtom1047
    Fin15AnchoredAtom1083 Fin15AnchoredAtom1728 Fin15AnchoredAtom3444 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12610
  ] at hbad
  tauto

theorem fin15Anchored_clause22974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom1032 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom3445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20802
  ] at hbad
  tauto

theorem fin15Anchored_clause22975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1034 Fin15AnchoredAtom3445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20802
  ] at hbad
  tauto

theorem fin15Anchored_clause22976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom3445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20802
  ] at hbad
  tauto

theorem fin15Anchored_clause22977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3445 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1729 Fin15AnchoredAtom3445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20802
  ] at hbad
  tauto

theorem fin15Anchored_clause22978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3445 chi ∧
      Fin15AnchoredAtom1032 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1032 Fin15AnchoredAtom1034 Fin15AnchoredAtom1048
    Fin15AnchoredAtom1084 Fin15AnchoredAtom1729 Fin15AnchoredAtom3445 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20802
  ] at hbad
  tauto

theorem fin15Anchored_clause22979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom1033 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom3446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24898
  ] at hbad
  tauto

theorem fin15Anchored_clause22980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom1034 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1034 Fin15AnchoredAtom3446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24898
  ] at hbad
  tauto

theorem fin15Anchored_clause22981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom3446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24898
  ] at hbad
  tauto

theorem fin15Anchored_clause22982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3446 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1730 Fin15AnchoredAtom3446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24898
  ] at hbad
  tauto

theorem fin15Anchored_clause22983 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3446 chi ∧
      Fin15AnchoredAtom1033 chi ∧
      Fin15AnchoredAtom1034 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1033 Fin15AnchoredAtom1034 Fin15AnchoredAtom1049
    Fin15AnchoredAtom1085 Fin15AnchoredAtom1730 Fin15AnchoredAtom3446 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24898
  ] at hbad
  tauto

theorem fin15Anchored_clause22984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3447 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom3447 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03650
  ] at hbad
  tauto

theorem fin15Anchored_clause22985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom3448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05698
  ] at hbad
  tauto

theorem fin15Anchored_clause22986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom3448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05698
  ] at hbad
  tauto

theorem fin15Anchored_clause22987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom3448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05698
  ] at hbad
  tauto

theorem fin15Anchored_clause22988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05698
  ] at hbad
  tauto

theorem fin15Anchored_clause22989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3448 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom3448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05698
  ] at hbad
  tauto

theorem fin15Anchored_clause22990 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3448 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom1037 Fin15AnchoredAtom1041
    Fin15AnchoredAtom1087 Fin15AnchoredAtom1732 Fin15AnchoredAtom3448 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05698
  ] at hbad
  tauto

theorem fin15Anchored_clause22991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom3449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09794
  ] at hbad
  tauto

theorem fin15Anchored_clause22992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom3449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09794
  ] at hbad
  tauto

theorem fin15Anchored_clause22993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom3449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09794
  ] at hbad
  tauto

theorem fin15Anchored_clause22994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09794
  ] at hbad
  tauto

theorem fin15Anchored_clause22995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3449 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom3449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09794
  ] at hbad
  tauto

theorem fin15Anchored_clause22996 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3449 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom1038 Fin15AnchoredAtom1042
    Fin15AnchoredAtom1088 Fin15AnchoredAtom1733 Fin15AnchoredAtom3449 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09794
  ] at hbad
  tauto

theorem fin15Anchored_clause22997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1035 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom3450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17986
  ] at hbad
  tauto

theorem fin15Anchored_clause22998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom3450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17986
  ] at hbad
  tauto

theorem fin15Anchored_clause22999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom3450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17986
  ] at hbad
  tauto

theorem fin15Anchored_clause23000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom3450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17986
  ] at hbad
  tauto

theorem fin15Anchored_clause23001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3450 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom3450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17986
  ] at hbad
  tauto

theorem fin15Anchored_clause23002 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3450 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1035 Fin15AnchoredAtom1039 Fin15AnchoredAtom1043
    Fin15AnchoredAtom1089 Fin15AnchoredAtom1734 Fin15AnchoredAtom3450 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17986
  ] at hbad
  tauto

theorem fin15Anchored_clause23003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3451 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom3451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06722
  ] at hbad
  tauto

theorem fin15Anchored_clause23004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3451 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom3451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06722
  ] at hbad
  tauto

theorem fin15Anchored_clause23005 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3451 chi ∧
      Fin15AnchoredAtom1036 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1044 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1036 Fin15AnchoredAtom1037 Fin15AnchoredAtom1044
    Fin15AnchoredAtom1090 Fin15AnchoredAtom1735 Fin15AnchoredAtom3451 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06722
  ] at hbad
  tauto

theorem fin15Anchored_clause23006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3452 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom3452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10818
  ] at hbad
  tauto

theorem fin15Anchored_clause23007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3452 chi ∧
      ¬Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1736 Fin15AnchoredAtom3452 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10818
  ] at hbad
  tauto

theorem fin15Anchored_clause23008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3453 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom3453 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19010
  ] at hbad
  tauto

theorem fin15Anchored_clause23009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom3454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12866
  ] at hbad
  tauto

theorem fin15Anchored_clause23010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom3454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12866
  ] at hbad
  tauto

theorem fin15Anchored_clause23011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom3454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12866
  ] at hbad
  tauto

theorem fin15Anchored_clause23012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12866
  ] at hbad
  tauto

theorem fin15Anchored_clause23013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3454 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom3454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12866
  ] at hbad
  tauto

theorem fin15Anchored_clause23014 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3454 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom1038 Fin15AnchoredAtom1047
    Fin15AnchoredAtom1093 Fin15AnchoredAtom1738 Fin15AnchoredAtom3454 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12866
  ] at hbad
  tauto

theorem fin15Anchored_clause23015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom3455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21058
  ] at hbad
  tauto

theorem fin15Anchored_clause23016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom3455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21058
  ] at hbad
  tauto

theorem fin15Anchored_clause23017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom3455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21058
  ] at hbad
  tauto

theorem fin15Anchored_clause23018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21058
  ] at hbad
  tauto

theorem fin15Anchored_clause23019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3455 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom3455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21058
  ] at hbad
  tauto

theorem fin15Anchored_clause23020 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3455 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom1039 Fin15AnchoredAtom1048
    Fin15AnchoredAtom1094 Fin15AnchoredAtom1739 Fin15AnchoredAtom3455 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21058
  ] at hbad
  tauto

theorem fin15Anchored_clause23021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom3456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25154
  ] at hbad
  tauto

theorem fin15Anchored_clause23022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom3456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25154
  ] at hbad
  tauto

theorem fin15Anchored_clause23023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom3456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25154
  ] at hbad
  tauto

theorem fin15Anchored_clause23024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom3456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25154
  ] at hbad
  tauto

theorem fin15Anchored_clause23025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3456 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom3456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25154
  ] at hbad
  tauto

theorem fin15Anchored_clause23026 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3456 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom1039 Fin15AnchoredAtom1049
    Fin15AnchoredAtom1095 Fin15AnchoredAtom1740 Fin15AnchoredAtom3456 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25154
  ] at hbad
  tauto

theorem fin15Anchored_clause23027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1040 Fin15AnchoredAtom3457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07234
  ] at hbad
  tauto

theorem fin15Anchored_clause23028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom3457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07234
  ] at hbad
  tauto

theorem fin15Anchored_clause23029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1044 Fin15AnchoredAtom3457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07234
  ] at hbad
  tauto

theorem fin15Anchored_clause23030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3457 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1741 Fin15AnchoredAtom3457 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07234
  ] at hbad
  tauto

theorem fin15Anchored_clause23031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3458 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1040 Fin15AnchoredAtom3458 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11330
  ] at hbad
  tauto

theorem fin15Anchored_clause23032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3458 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom3458 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11330
  ] at hbad
  tauto

theorem fin15Anchored_clause23033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3459 chi ∧
      ¬Fin15AnchoredAtom1040 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1040 Fin15AnchoredAtom3459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19522
  ] at hbad
  tauto

theorem fin15Anchored_clause23034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3459 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom3459 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19522
  ] at hbad
  tauto

theorem fin15Anchored_clause23035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom3460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13378
  ] at hbad
  tauto

theorem fin15Anchored_clause23036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom3460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13378
  ] at hbad
  tauto

theorem fin15Anchored_clause23037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom3460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13378
  ] at hbad
  tauto

theorem fin15Anchored_clause23038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13378
  ] at hbad
  tauto

theorem fin15Anchored_clause23039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3460 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom3460 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13378
  ] at hbad
  tauto

end ErdosSzekeres

end
