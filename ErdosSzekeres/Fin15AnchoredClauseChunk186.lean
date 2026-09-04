module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 186. -/

theorem fin15Anchored_clause23808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom3659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09356
  ] at hbad
  tauto

theorem fin15Anchored_clause23809 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1283 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1283 Fin15AnchoredAtom3659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09356
  ] at hbad
  tauto

theorem fin15Anchored_clause23810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1448 Fin15AnchoredAtom3659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09356
  ] at hbad
  tauto

theorem fin15Anchored_clause23811 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3659 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1283 chi ∧
      Fin15AnchoredAtom1448 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom1138 Fin15AnchoredAtom1153
    Fin15AnchoredAtom1283 Fin15AnchoredAtom1448 Fin15AnchoredAtom3659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09356
  ] at hbad
  tauto

theorem fin15Anchored_clause23812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom3660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17548
  ] at hbad
  tauto

theorem fin15Anchored_clause23813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom3660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17548
  ] at hbad
  tauto

theorem fin15Anchored_clause23814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1154 Fin15AnchoredAtom3660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17548
  ] at hbad
  tauto

theorem fin15Anchored_clause23815 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1284 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1284 Fin15AnchoredAtom3660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17548
  ] at hbad
  tauto

theorem fin15Anchored_clause23816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3660 chi ∧
      ¬Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1449 Fin15AnchoredAtom3660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17548
  ] at hbad
  tauto

theorem fin15Anchored_clause23817 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3660 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1284 chi ∧
      Fin15AnchoredAtom1449 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom1139 Fin15AnchoredAtom1154
    Fin15AnchoredAtom1284 Fin15AnchoredAtom1449 Fin15AnchoredAtom3660 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17548
  ] at hbad
  tauto

theorem fin15Anchored_clause23818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3661 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom3661 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06284
  ] at hbad
  tauto

theorem fin15Anchored_clause23819 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3661 chi ∧
      ¬Fin15AnchoredAtom1155 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1155 Fin15AnchoredAtom3661 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06284
  ] at hbad
  tauto

theorem fin15Anchored_clause23820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3663 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom3663 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18572
  ] at hbad
  tauto

theorem fin15Anchored_clause23821 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3663 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1157 chi ∧
      Fin15AnchoredAtom1287 chi ∧
      Fin15AnchoredAtom1452 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1136 Fin15AnchoredAtom1139 Fin15AnchoredAtom1157
    Fin15AnchoredAtom1287 Fin15AnchoredAtom1452 Fin15AnchoredAtom3663 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18572
  ] at hbad
  tauto

theorem fin15Anchored_clause23822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom3664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12428
  ] at hbad
  tauto

theorem fin15Anchored_clause23823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom3664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12428
  ] at hbad
  tauto

theorem fin15Anchored_clause23824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom3664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12428
  ] at hbad
  tauto

theorem fin15Anchored_clause23825 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1288 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1288 Fin15AnchoredAtom3664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12428
  ] at hbad
  tauto

theorem fin15Anchored_clause23826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3664 chi ∧
      ¬Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1453 Fin15AnchoredAtom3664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12428
  ] at hbad
  tauto

theorem fin15Anchored_clause23827 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3664 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1288 chi ∧
      Fin15AnchoredAtom1453 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom1138 Fin15AnchoredAtom1158
    Fin15AnchoredAtom1288 Fin15AnchoredAtom1453 Fin15AnchoredAtom3664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12428
  ] at hbad
  tauto

theorem fin15Anchored_clause23828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom3665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20620
  ] at hbad
  tauto

theorem fin15Anchored_clause23829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom3665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20620
  ] at hbad
  tauto

theorem fin15Anchored_clause23830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1159 Fin15AnchoredAtom3665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20620
  ] at hbad
  tauto

theorem fin15Anchored_clause23831 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1289 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1289 Fin15AnchoredAtom3665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20620
  ] at hbad
  tauto

theorem fin15Anchored_clause23832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3665 chi ∧
      ¬Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1454 Fin15AnchoredAtom3665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20620
  ] at hbad
  tauto

theorem fin15Anchored_clause23833 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3665 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1289 chi ∧
      Fin15AnchoredAtom1454 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom1139 Fin15AnchoredAtom1159
    Fin15AnchoredAtom1289 Fin15AnchoredAtom1454 Fin15AnchoredAtom3665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20620
  ] at hbad
  tauto

theorem fin15Anchored_clause23834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom3666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24716
  ] at hbad
  tauto

theorem fin15Anchored_clause23835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom3666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24716
  ] at hbad
  tauto

theorem fin15Anchored_clause23836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1160 Fin15AnchoredAtom3666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24716
  ] at hbad
  tauto

theorem fin15Anchored_clause23837 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1290 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1290 Fin15AnchoredAtom3666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24716
  ] at hbad
  tauto

theorem fin15Anchored_clause23838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3666 chi ∧
      ¬Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1455 Fin15AnchoredAtom3666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24716
  ] at hbad
  tauto

theorem fin15Anchored_clause23839 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3666 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1290 chi ∧
      Fin15AnchoredAtom1455 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom1139 Fin15AnchoredAtom1160
    Fin15AnchoredAtom1290 Fin15AnchoredAtom1455 Fin15AnchoredAtom3666 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24716
  ] at hbad
  tauto

theorem fin15Anchored_clause23840 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3667 chi ∧
      Fin15AnchoredAtom1140 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1291 chi ∧
      Fin15AnchoredAtom1456 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1140 Fin15AnchoredAtom1141 Fin15AnchoredAtom1146
    Fin15AnchoredAtom1291 Fin15AnchoredAtom1456 Fin15AnchoredAtom3667 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01804
  ] at hbad
  tauto

theorem fin15Anchored_clause23841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3673 chi ∧
      ¬Fin15AnchoredAtom1462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1462 Fin15AnchoredAtom3673 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05388
  ] at hbad
  tauto

theorem fin15Anchored_clause23842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3674 chi ∧
      ¬Fin15AnchoredAtom1463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1463 Fin15AnchoredAtom3674 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09484
  ] at hbad
  tauto

theorem fin15Anchored_clause23843 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3679 chi ∧
      ¬Fin15AnchoredAtom1303 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1303 Fin15AnchoredAtom3679 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12556
  ] at hbad
  tauto

theorem fin15Anchored_clause23844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom3682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03596
  ] at hbad
  tauto

theorem fin15Anchored_clause23845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1147 Fin15AnchoredAtom3682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03596
  ] at hbad
  tauto

theorem fin15Anchored_clause23846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1151 Fin15AnchoredAtom3682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03596
  ] at hbad
  tauto

theorem fin15Anchored_clause23847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1306 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1306 Fin15AnchoredAtom3682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03596
  ] at hbad
  tauto

theorem fin15Anchored_clause23848 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3682 chi ∧
      ¬Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1471 Fin15AnchoredAtom3682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03596
  ] at hbad
  tauto

theorem fin15Anchored_clause23849 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3682 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1147 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1306 chi ∧
      Fin15AnchoredAtom1471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom1147 Fin15AnchoredAtom1151
    Fin15AnchoredAtom1306 Fin15AnchoredAtom1471 Fin15AnchoredAtom3682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03596
  ] at hbad
  tauto

theorem fin15Anchored_clause23850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom3683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05644
  ] at hbad
  tauto

theorem fin15Anchored_clause23851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom3683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05644
  ] at hbad
  tauto

theorem fin15Anchored_clause23852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom3683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05644
  ] at hbad
  tauto

theorem fin15Anchored_clause23853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1307 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom3683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05644
  ] at hbad
  tauto

theorem fin15Anchored_clause23854 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3683 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom3683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05644
  ] at hbad
  tauto

theorem fin15Anchored_clause23855 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3683 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom1148 Fin15AnchoredAtom1152
    Fin15AnchoredAtom1307 Fin15AnchoredAtom1472 Fin15AnchoredAtom3683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05644
  ] at hbad
  tauto

theorem fin15Anchored_clause23856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom3684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09740
  ] at hbad
  tauto

theorem fin15Anchored_clause23857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom3684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09740
  ] at hbad
  tauto

theorem fin15Anchored_clause23858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom3684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09740
  ] at hbad
  tauto

theorem fin15Anchored_clause23859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom3684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09740
  ] at hbad
  tauto

theorem fin15Anchored_clause23860 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3684 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom3684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09740
  ] at hbad
  tauto

theorem fin15Anchored_clause23861 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3684 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom1149 Fin15AnchoredAtom1153
    Fin15AnchoredAtom1308 Fin15AnchoredAtom1473 Fin15AnchoredAtom3684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09740
  ] at hbad
  tauto

theorem fin15Anchored_clause23862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom3685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17932
  ] at hbad
  tauto

theorem fin15Anchored_clause23863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom3685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17932
  ] at hbad
  tauto

theorem fin15Anchored_clause23864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1154 Fin15AnchoredAtom3685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17932
  ] at hbad
  tauto

theorem fin15Anchored_clause23865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom3685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17932
  ] at hbad
  tauto

theorem fin15Anchored_clause23866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3685 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom3685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17932
  ] at hbad
  tauto

theorem fin15Anchored_clause23867 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3685 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom1150 Fin15AnchoredAtom1154
    Fin15AnchoredAtom1309 Fin15AnchoredAtom1474 Fin15AnchoredAtom3685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17932
  ] at hbad
  tauto

theorem fin15Anchored_clause23868 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom3686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06668
  ] at hbad
  tauto

theorem fin15Anchored_clause23869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom1155 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1155 Fin15AnchoredAtom3686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06668
  ] at hbad
  tauto

theorem fin15Anchored_clause23870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1310 Fin15AnchoredAtom3686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06668
  ] at hbad
  tauto

theorem fin15Anchored_clause23871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3686 chi ∧
      ¬Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1475 Fin15AnchoredAtom3686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06668
  ] at hbad
  tauto

theorem fin15Anchored_clause23872 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3686 chi ∧
      Fin15AnchoredAtom1147 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1155 chi ∧
      Fin15AnchoredAtom1310 chi ∧
      Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1147 Fin15AnchoredAtom1148 Fin15AnchoredAtom1155
    Fin15AnchoredAtom1310 Fin15AnchoredAtom1475 Fin15AnchoredAtom3686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06668
  ] at hbad
  tauto

theorem fin15Anchored_clause23873 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom3687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10764
  ] at hbad
  tauto

theorem fin15Anchored_clause23874 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom1311 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1311 Fin15AnchoredAtom3687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10764
  ] at hbad
  tauto

theorem fin15Anchored_clause23875 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3687 chi ∧
      ¬Fin15AnchoredAtom1476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1476 Fin15AnchoredAtom3687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10764
  ] at hbad
  tauto

theorem fin15Anchored_clause23876 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3688 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom3688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18956
  ] at hbad
  tauto

theorem fin15Anchored_clause23877 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3688 chi ∧
      ¬Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1312 Fin15AnchoredAtom3688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18956
  ] at hbad
  tauto

theorem fin15Anchored_clause23878 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom3689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12812
  ] at hbad
  tauto

theorem fin15Anchored_clause23879 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom3689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12812
  ] at hbad
  tauto

theorem fin15Anchored_clause23880 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom3689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12812
  ] at hbad
  tauto

theorem fin15Anchored_clause23881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom3689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12812
  ] at hbad
  tauto

theorem fin15Anchored_clause23882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3689 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom3689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12812
  ] at hbad
  tauto

theorem fin15Anchored_clause23883 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3689 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom1149 Fin15AnchoredAtom1158
    Fin15AnchoredAtom1313 Fin15AnchoredAtom1478 Fin15AnchoredAtom3689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12812
  ] at hbad
  tauto

theorem fin15Anchored_clause23884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom3690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21004
  ] at hbad
  tauto

theorem fin15Anchored_clause23885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom3690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21004
  ] at hbad
  tauto

theorem fin15Anchored_clause23886 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1159 Fin15AnchoredAtom3690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21004
  ] at hbad
  tauto

theorem fin15Anchored_clause23887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom3690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21004
  ] at hbad
  tauto

theorem fin15Anchored_clause23888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3690 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom3690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21004
  ] at hbad
  tauto

theorem fin15Anchored_clause23889 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3690 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom1150 Fin15AnchoredAtom1159
    Fin15AnchoredAtom1314 Fin15AnchoredAtom1479 Fin15AnchoredAtom3690 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21004
  ] at hbad
  tauto

theorem fin15Anchored_clause23890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom3691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25100
  ] at hbad
  tauto

theorem fin15Anchored_clause23891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom3691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25100
  ] at hbad
  tauto

theorem fin15Anchored_clause23892 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1160 Fin15AnchoredAtom3691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25100
  ] at hbad
  tauto

theorem fin15Anchored_clause23893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1315 Fin15AnchoredAtom3691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25100
  ] at hbad
  tauto

theorem fin15Anchored_clause23894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3691 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom3691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25100
  ] at hbad
  tauto

theorem fin15Anchored_clause23895 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3691 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom1150 Fin15AnchoredAtom1160
    Fin15AnchoredAtom1315 Fin15AnchoredAtom1480 Fin15AnchoredAtom3691 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25100
  ] at hbad
  tauto

theorem fin15Anchored_clause23896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3692 chi ∧
      ¬Fin15AnchoredAtom1316 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1316 Fin15AnchoredAtom3692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07180
  ] at hbad
  tauto

theorem fin15Anchored_clause23897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3692 chi ∧
      ¬Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1481 Fin15AnchoredAtom3692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07180
  ] at hbad
  tauto

theorem fin15Anchored_clause23898 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3692 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1155 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1151 Fin15AnchoredAtom1152 Fin15AnchoredAtom1155
    Fin15AnchoredAtom1316 Fin15AnchoredAtom1481 Fin15AnchoredAtom3692 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07180
  ] at hbad
  tauto

theorem fin15Anchored_clause23899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom3693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11276
  ] at hbad
  tauto

theorem fin15Anchored_clause23900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1156 Fin15AnchoredAtom3693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11276
  ] at hbad
  tauto

theorem fin15Anchored_clause23901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom1317 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1317 Fin15AnchoredAtom3693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11276
  ] at hbad
  tauto

theorem fin15Anchored_clause23902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3693 chi ∧
      ¬Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1482 Fin15AnchoredAtom3693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11276
  ] at hbad
  tauto

theorem fin15Anchored_clause23903 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3693 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1156 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1151 Fin15AnchoredAtom1153 Fin15AnchoredAtom1156
    Fin15AnchoredAtom1317 Fin15AnchoredAtom1482 Fin15AnchoredAtom3693 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11276
  ] at hbad
  tauto

theorem fin15Anchored_clause23904 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3694 chi ∧
      ¬Fin15AnchoredAtom1483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1483 Fin15AnchoredAtom3694 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19468
  ] at hbad
  tauto

theorem fin15Anchored_clause23905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom3695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13324
  ] at hbad
  tauto

theorem fin15Anchored_clause23906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom3695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13324
  ] at hbad
  tauto

theorem fin15Anchored_clause23907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom3695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13324
  ] at hbad
  tauto

theorem fin15Anchored_clause23908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom3695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13324
  ] at hbad
  tauto

theorem fin15Anchored_clause23909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3695 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom3695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13324
  ] at hbad
  tauto

theorem fin15Anchored_clause23910 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3695 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom1153 Fin15AnchoredAtom1158
    Fin15AnchoredAtom1319 Fin15AnchoredAtom1484 Fin15AnchoredAtom3695 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13324
  ] at hbad
  tauto

theorem fin15Anchored_clause23911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom3696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21516
  ] at hbad
  tauto

theorem fin15Anchored_clause23912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1154 Fin15AnchoredAtom3696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21516
  ] at hbad
  tauto

theorem fin15Anchored_clause23913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1159 Fin15AnchoredAtom3696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21516
  ] at hbad
  tauto

theorem fin15Anchored_clause23914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom3696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21516
  ] at hbad
  tauto

theorem fin15Anchored_clause23915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3696 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom3696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21516
  ] at hbad
  tauto

theorem fin15Anchored_clause23916 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3696 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom1154 Fin15AnchoredAtom1159
    Fin15AnchoredAtom1320 Fin15AnchoredAtom1485 Fin15AnchoredAtom3696 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21516
  ] at hbad
  tauto

theorem fin15Anchored_clause23917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom3697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25612
  ] at hbad
  tauto

theorem fin15Anchored_clause23918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1154 Fin15AnchoredAtom3697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25612
  ] at hbad
  tauto

theorem fin15Anchored_clause23919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1160 Fin15AnchoredAtom3697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25612
  ] at hbad
  tauto

theorem fin15Anchored_clause23920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom3697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25612
  ] at hbad
  tauto

theorem fin15Anchored_clause23921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3697 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom3697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25612
  ] at hbad
  tauto

theorem fin15Anchored_clause23922 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3697 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom1154 Fin15AnchoredAtom1160
    Fin15AnchoredAtom1321 Fin15AnchoredAtom1486 Fin15AnchoredAtom3697 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25612
  ] at hbad
  tauto

theorem fin15Anchored_clause23923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3698 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom3698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14348
  ] at hbad
  tauto

theorem fin15Anchored_clause23924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3698 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1322 Fin15AnchoredAtom3698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14348
  ] at hbad
  tauto

theorem fin15Anchored_clause23925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3698 chi ∧
      ¬Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1487 Fin15AnchoredAtom3698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14348
  ] at hbad
  tauto

theorem fin15Anchored_clause23926 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3698 chi ∧
      Fin15AnchoredAtom1155 chi ∧
      Fin15AnchoredAtom1156 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1322 chi ∧
      Fin15AnchoredAtom1487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1155 Fin15AnchoredAtom1156 Fin15AnchoredAtom1158
    Fin15AnchoredAtom1322 Fin15AnchoredAtom1487 Fin15AnchoredAtom3698 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14348
  ] at hbad
  tauto

theorem fin15Anchored_clause23927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3699 chi ∧
      ¬Fin15AnchoredAtom1155 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1155 Fin15AnchoredAtom3699 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22540
  ] at hbad
  tauto

theorem fin15Anchored_clause23928 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3699 chi ∧
      ¬Fin15AnchoredAtom1157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1157 Fin15AnchoredAtom3699 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22540
  ] at hbad
  tauto

theorem fin15Anchored_clause23929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3699 chi ∧
      ¬Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1323 Fin15AnchoredAtom3699 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22540
  ] at hbad
  tauto

theorem fin15Anchored_clause23930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3699 chi ∧
      ¬Fin15AnchoredAtom1488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1488 Fin15AnchoredAtom3699 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22540
  ] at hbad
  tauto

theorem fin15Anchored_clause23931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom3701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28684
  ] at hbad
  tauto

theorem fin15Anchored_clause23932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1159 Fin15AnchoredAtom3701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28684
  ] at hbad
  tauto

theorem fin15Anchored_clause23933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1160 Fin15AnchoredAtom3701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28684
  ] at hbad
  tauto

theorem fin15Anchored_clause23934 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom3701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28684
  ] at hbad
  tauto

theorem fin15Anchored_clause23935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3701 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom3701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28684
  ] at hbad
  tauto

end ErdosSzekeres

end
