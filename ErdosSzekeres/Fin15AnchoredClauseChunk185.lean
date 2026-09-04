module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 185. -/

theorem fin15Anchored_clause23680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom3624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16588
  ] at hbad
  tauto

theorem fin15Anchored_clause23681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom3624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16588
  ] at hbad
  tauto

theorem fin15Anchored_clause23682 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom3624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16588
  ] at hbad
  tauto

theorem fin15Anchored_clause23683 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3624 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom1132 Fin15AnchoredAtom1139
    Fin15AnchoredAtom1248 Fin15AnchoredAtom1413 Fin15AnchoredAtom3624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16588
  ] at hbad
  tauto

theorem fin15Anchored_clause23684 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3625 chi ∧
      Fin15AnchoredAtom1126 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1140 chi ∧
      Fin15AnchoredAtom1249 chi ∧
      Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1126 Fin15AnchoredAtom1127 Fin15AnchoredAtom1140
    Fin15AnchoredAtom1249 Fin15AnchoredAtom1414 Fin15AnchoredAtom3625 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00844
  ] at hbad
  tauto

theorem fin15Anchored_clause23685 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3626 chi ∧
      Fin15AnchoredAtom1126 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1250 chi ∧
      Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1126 Fin15AnchoredAtom1128 Fin15AnchoredAtom1141
    Fin15AnchoredAtom1250 Fin15AnchoredAtom1415 Fin15AnchoredAtom3626 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01356
  ] at hbad
  tauto

theorem fin15Anchored_clause23686 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3628 chi ∧
      Fin15AnchoredAtom1126 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1143 chi ∧
      Fin15AnchoredAtom1252 chi ∧
      Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1126 Fin15AnchoredAtom1130 Fin15AnchoredAtom1143
    Fin15AnchoredAtom1252 Fin15AnchoredAtom1417 Fin15AnchoredAtom3628 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04428
  ] at hbad
  tauto

theorem fin15Anchored_clause23687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3629 chi ∧
      ¬Fin15AnchoredAtom1144 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1144 Fin15AnchoredAtom3629 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08524
  ] at hbad
  tauto

theorem fin15Anchored_clause23688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3630 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom3630 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16716
  ] at hbad
  tauto

theorem fin15Anchored_clause23689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom3631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01612
  ] at hbad
  tauto

theorem fin15Anchored_clause23690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom3631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01612
  ] at hbad
  tauto

theorem fin15Anchored_clause23691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom3631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01612
  ] at hbad
  tauto

theorem fin15Anchored_clause23692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom3631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01612
  ] at hbad
  tauto

theorem fin15Anchored_clause23693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3631 chi ∧
      ¬Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1420 Fin15AnchoredAtom3631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01612
  ] at hbad
  tauto

theorem fin15Anchored_clause23694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3631 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom1128 Fin15AnchoredAtom1146
    Fin15AnchoredAtom1255 Fin15AnchoredAtom1420 Fin15AnchoredAtom3631 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01612
  ] at hbad
  tauto

theorem fin15Anchored_clause23695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom3632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02636
  ] at hbad
  tauto

theorem fin15Anchored_clause23696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom1256 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1256 Fin15AnchoredAtom3632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02636
  ] at hbad
  tauto

theorem fin15Anchored_clause23697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3632 chi ∧
      ¬Fin15AnchoredAtom1421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1421 Fin15AnchoredAtom3632 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02636
  ] at hbad
  tauto

theorem fin15Anchored_clause23698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom3633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04684
  ] at hbad
  tauto

theorem fin15Anchored_clause23699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom3633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04684
  ] at hbad
  tauto

theorem fin15Anchored_clause23700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom3633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04684
  ] at hbad
  tauto

theorem fin15Anchored_clause23701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom3633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04684
  ] at hbad
  tauto

theorem fin15Anchored_clause23702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3633 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom3633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04684
  ] at hbad
  tauto

theorem fin15Anchored_clause23703 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3633 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom1130 Fin15AnchoredAtom1148
    Fin15AnchoredAtom1257 Fin15AnchoredAtom1422 Fin15AnchoredAtom3633 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04684
  ] at hbad
  tauto

theorem fin15Anchored_clause23704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom3634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08780
  ] at hbad
  tauto

theorem fin15Anchored_clause23705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom3634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08780
  ] at hbad
  tauto

theorem fin15Anchored_clause23706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom3634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08780
  ] at hbad
  tauto

theorem fin15Anchored_clause23707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom3634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08780
  ] at hbad
  tauto

theorem fin15Anchored_clause23708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3634 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom3634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08780
  ] at hbad
  tauto

theorem fin15Anchored_clause23709 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3634 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom1131 Fin15AnchoredAtom1149
    Fin15AnchoredAtom1258 Fin15AnchoredAtom1423 Fin15AnchoredAtom3634 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08780
  ] at hbad
  tauto

theorem fin15Anchored_clause23710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom3635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16972
  ] at hbad
  tauto

theorem fin15Anchored_clause23711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom3635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16972
  ] at hbad
  tauto

theorem fin15Anchored_clause23712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom3635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16972
  ] at hbad
  tauto

theorem fin15Anchored_clause23713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1259 Fin15AnchoredAtom3635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16972
  ] at hbad
  tauto

theorem fin15Anchored_clause23714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3635 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom3635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16972
  ] at hbad
  tauto

theorem fin15Anchored_clause23715 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3635 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom1132 Fin15AnchoredAtom1150
    Fin15AnchoredAtom1259 Fin15AnchoredAtom1424 Fin15AnchoredAtom3635 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16972
  ] at hbad
  tauto

theorem fin15Anchored_clause23716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3636 chi ∧
      ¬Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1129 Fin15AnchoredAtom3636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03148
  ] at hbad
  tauto

theorem fin15Anchored_clause23717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3636 chi ∧
      ¬Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1425 Fin15AnchoredAtom3636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03148
  ] at hbad
  tauto

theorem fin15Anchored_clause23718 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3636 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1129 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom1129 Fin15AnchoredAtom1151
    Fin15AnchoredAtom1260 Fin15AnchoredAtom1425 Fin15AnchoredAtom3636 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03148
  ] at hbad
  tauto

theorem fin15Anchored_clause23719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom3637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05196
  ] at hbad
  tauto

theorem fin15Anchored_clause23720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom3637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05196
  ] at hbad
  tauto

theorem fin15Anchored_clause23721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom3637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05196
  ] at hbad
  tauto

theorem fin15Anchored_clause23722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom3637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05196
  ] at hbad
  tauto

theorem fin15Anchored_clause23723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3637 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom3637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05196
  ] at hbad
  tauto

theorem fin15Anchored_clause23724 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3637 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom1130 Fin15AnchoredAtom1152
    Fin15AnchoredAtom1261 Fin15AnchoredAtom1426 Fin15AnchoredAtom3637 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05196
  ] at hbad
  tauto

theorem fin15Anchored_clause23725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom3638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09292
  ] at hbad
  tauto

theorem fin15Anchored_clause23726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom3638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09292
  ] at hbad
  tauto

theorem fin15Anchored_clause23727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom3638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09292
  ] at hbad
  tauto

theorem fin15Anchored_clause23728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom3638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09292
  ] at hbad
  tauto

theorem fin15Anchored_clause23729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3638 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom3638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09292
  ] at hbad
  tauto

theorem fin15Anchored_clause23730 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3638 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom1131 Fin15AnchoredAtom1153
    Fin15AnchoredAtom1262 Fin15AnchoredAtom1427 Fin15AnchoredAtom3638 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09292
  ] at hbad
  tauto

theorem fin15Anchored_clause23731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom3639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17484
  ] at hbad
  tauto

theorem fin15Anchored_clause23732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom3639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17484
  ] at hbad
  tauto

theorem fin15Anchored_clause23733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1154 Fin15AnchoredAtom3639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17484
  ] at hbad
  tauto

theorem fin15Anchored_clause23734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom3639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17484
  ] at hbad
  tauto

theorem fin15Anchored_clause23735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3639 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom3639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17484
  ] at hbad
  tauto

theorem fin15Anchored_clause23736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3639 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom1132 Fin15AnchoredAtom1154
    Fin15AnchoredAtom1263 Fin15AnchoredAtom1428 Fin15AnchoredAtom3639 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17484
  ] at hbad
  tauto

theorem fin15Anchored_clause23737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3640 chi ∧
      ¬Fin15AnchoredAtom1429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1429 Fin15AnchoredAtom3640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06220
  ] at hbad
  tauto

theorem fin15Anchored_clause23738 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3640 chi ∧
      Fin15AnchoredAtom1129 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1155 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1129 Fin15AnchoredAtom1130 Fin15AnchoredAtom1155
    Fin15AnchoredAtom1264 Fin15AnchoredAtom1429 Fin15AnchoredAtom3640 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06220
  ] at hbad
  tauto

theorem fin15Anchored_clause23739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3641 chi ∧
      ¬Fin15AnchoredAtom1129 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1129 Fin15AnchoredAtom3641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10316
  ] at hbad
  tauto

theorem fin15Anchored_clause23740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3641 chi ∧
      ¬Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1156 Fin15AnchoredAtom3641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10316
  ] at hbad
  tauto

theorem fin15Anchored_clause23741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3641 chi ∧
      ¬Fin15AnchoredAtom1430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1430 Fin15AnchoredAtom3641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10316
  ] at hbad
  tauto

theorem fin15Anchored_clause23742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3641 chi ∧
      Fin15AnchoredAtom1129 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1156 chi ∧
      Fin15AnchoredAtom1265 chi ∧
      Fin15AnchoredAtom1430 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1129 Fin15AnchoredAtom1131 Fin15AnchoredAtom1156
    Fin15AnchoredAtom1265 Fin15AnchoredAtom1430 Fin15AnchoredAtom3641 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10316
  ] at hbad
  tauto

theorem fin15Anchored_clause23743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3642 chi ∧
      ¬Fin15AnchoredAtom1266 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1266 Fin15AnchoredAtom3642 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18508
  ] at hbad
  tauto

theorem fin15Anchored_clause23744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom3643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12364
  ] at hbad
  tauto

theorem fin15Anchored_clause23745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom3643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12364
  ] at hbad
  tauto

theorem fin15Anchored_clause23746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom3643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12364
  ] at hbad
  tauto

theorem fin15Anchored_clause23747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom3643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12364
  ] at hbad
  tauto

theorem fin15Anchored_clause23748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3643 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom3643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12364
  ] at hbad
  tauto

theorem fin15Anchored_clause23749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3643 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom1131 Fin15AnchoredAtom1158
    Fin15AnchoredAtom1267 Fin15AnchoredAtom1432 Fin15AnchoredAtom3643 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12364
  ] at hbad
  tauto

theorem fin15Anchored_clause23750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom3644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20556
  ] at hbad
  tauto

theorem fin15Anchored_clause23751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom3644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20556
  ] at hbad
  tauto

theorem fin15Anchored_clause23752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1159 Fin15AnchoredAtom3644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20556
  ] at hbad
  tauto

theorem fin15Anchored_clause23753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom3644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20556
  ] at hbad
  tauto

theorem fin15Anchored_clause23754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3644 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom3644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20556
  ] at hbad
  tauto

theorem fin15Anchored_clause23755 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3644 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom1132 Fin15AnchoredAtom1159
    Fin15AnchoredAtom1268 Fin15AnchoredAtom1433 Fin15AnchoredAtom3644 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20556
  ] at hbad
  tauto

theorem fin15Anchored_clause23756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom3645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24652
  ] at hbad
  tauto

theorem fin15Anchored_clause23757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom3645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24652
  ] at hbad
  tauto

theorem fin15Anchored_clause23758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1160 Fin15AnchoredAtom3645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24652
  ] at hbad
  tauto

theorem fin15Anchored_clause23759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1269 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1269 Fin15AnchoredAtom3645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24652
  ] at hbad
  tauto

theorem fin15Anchored_clause23760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3645 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom3645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24652
  ] at hbad
  tauto

theorem fin15Anchored_clause23761 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3645 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1132 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1269 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom1132 Fin15AnchoredAtom1160
    Fin15AnchoredAtom1269 Fin15AnchoredAtom1434 Fin15AnchoredAtom3645 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24652
  ] at hbad
  tauto

theorem fin15Anchored_clause23762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3647 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom3647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01420
  ] at hbad
  tauto

theorem fin15Anchored_clause23763 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3647 chi ∧
      Fin15AnchoredAtom1133 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1271 chi ∧
      Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1133 Fin15AnchoredAtom1135 Fin15AnchoredAtom1141
    Fin15AnchoredAtom1271 Fin15AnchoredAtom1436 Fin15AnchoredAtom3647 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01420
  ] at hbad
  tauto

theorem fin15Anchored_clause23764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3650 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom3650 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08588
  ] at hbad
  tauto

theorem fin15Anchored_clause23765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3651 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom3651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16780
  ] at hbad
  tauto

theorem fin15Anchored_clause23766 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3651 chi ∧
      Fin15AnchoredAtom1133 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1145 chi ∧
      Fin15AnchoredAtom1275 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1133 Fin15AnchoredAtom1139 Fin15AnchoredAtom1145
    Fin15AnchoredAtom1275 Fin15AnchoredAtom1440 Fin15AnchoredAtom3651 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16780
  ] at hbad
  tauto

theorem fin15Anchored_clause23767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom3652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01676
  ] at hbad
  tauto

theorem fin15Anchored_clause23768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom3652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01676
  ] at hbad
  tauto

theorem fin15Anchored_clause23769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom3652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01676
  ] at hbad
  tauto

theorem fin15Anchored_clause23770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1276 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1276 Fin15AnchoredAtom3652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01676
  ] at hbad
  tauto

theorem fin15Anchored_clause23771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3652 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom3652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01676
  ] at hbad
  tauto

theorem fin15Anchored_clause23772 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3652 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1276 chi ∧
      Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom1135 Fin15AnchoredAtom1146
    Fin15AnchoredAtom1276 Fin15AnchoredAtom1441 Fin15AnchoredAtom3652 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01676
  ] at hbad
  tauto

theorem fin15Anchored_clause23773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3653 chi ∧
      ¬Fin15AnchoredAtom1277 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1277 Fin15AnchoredAtom3653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02700
  ] at hbad
  tauto

theorem fin15Anchored_clause23774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3653 chi ∧
      ¬Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1442 Fin15AnchoredAtom3653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02700
  ] at hbad
  tauto

theorem fin15Anchored_clause23775 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3653 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1147 chi ∧
      Fin15AnchoredAtom1277 chi ∧
      Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom1136 Fin15AnchoredAtom1147
    Fin15AnchoredAtom1277 Fin15AnchoredAtom1442 Fin15AnchoredAtom3653 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02700
  ] at hbad
  tauto

theorem fin15Anchored_clause23776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom3654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04748
  ] at hbad
  tauto

theorem fin15Anchored_clause23777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom3654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04748
  ] at hbad
  tauto

theorem fin15Anchored_clause23778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom3654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04748
  ] at hbad
  tauto

theorem fin15Anchored_clause23779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1278 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1278 Fin15AnchoredAtom3654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04748
  ] at hbad
  tauto

theorem fin15Anchored_clause23780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3654 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom3654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04748
  ] at hbad
  tauto

theorem fin15Anchored_clause23781 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3654 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1278 chi ∧
      Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom1137 Fin15AnchoredAtom1148
    Fin15AnchoredAtom1278 Fin15AnchoredAtom1443 Fin15AnchoredAtom3654 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04748
  ] at hbad
  tauto

theorem fin15Anchored_clause23782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom3655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08844
  ] at hbad
  tauto

theorem fin15Anchored_clause23783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom3655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08844
  ] at hbad
  tauto

theorem fin15Anchored_clause23784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom3655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08844
  ] at hbad
  tauto

theorem fin15Anchored_clause23785 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1279 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1279 Fin15AnchoredAtom3655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08844
  ] at hbad
  tauto

theorem fin15Anchored_clause23786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3655 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom3655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08844
  ] at hbad
  tauto

theorem fin15Anchored_clause23787 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3655 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1279 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom1138 Fin15AnchoredAtom1149
    Fin15AnchoredAtom1279 Fin15AnchoredAtom1444 Fin15AnchoredAtom3655 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08844
  ] at hbad
  tauto

theorem fin15Anchored_clause23788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom3656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17036
  ] at hbad
  tauto

theorem fin15Anchored_clause23789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom3656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17036
  ] at hbad
  tauto

theorem fin15Anchored_clause23790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom3656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17036
  ] at hbad
  tauto

theorem fin15Anchored_clause23791 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1280 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1280 Fin15AnchoredAtom3656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17036
  ] at hbad
  tauto

theorem fin15Anchored_clause23792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3656 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom3656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17036
  ] at hbad
  tauto

theorem fin15Anchored_clause23793 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3656 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1280 chi ∧
      Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom1139 Fin15AnchoredAtom1150
    Fin15AnchoredAtom1280 Fin15AnchoredAtom1445 Fin15AnchoredAtom3656 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17036
  ] at hbad
  tauto

theorem fin15Anchored_clause23794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom3657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03212
  ] at hbad
  tauto

theorem fin15Anchored_clause23795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1136 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1136 Fin15AnchoredAtom3657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03212
  ] at hbad
  tauto

theorem fin15Anchored_clause23796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1151 Fin15AnchoredAtom3657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03212
  ] at hbad
  tauto

theorem fin15Anchored_clause23797 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1281 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1281 Fin15AnchoredAtom3657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03212
  ] at hbad
  tauto

theorem fin15Anchored_clause23798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3657 chi ∧
      ¬Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1446 Fin15AnchoredAtom3657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03212
  ] at hbad
  tauto

theorem fin15Anchored_clause23799 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3657 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1281 chi ∧
      Fin15AnchoredAtom1446 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom1136 Fin15AnchoredAtom1151
    Fin15AnchoredAtom1281 Fin15AnchoredAtom1446 Fin15AnchoredAtom3657 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03212
  ] at hbad
  tauto

theorem fin15Anchored_clause23800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom3658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05260
  ] at hbad
  tauto

theorem fin15Anchored_clause23801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom3658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05260
  ] at hbad
  tauto

theorem fin15Anchored_clause23802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom3658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05260
  ] at hbad
  tauto

theorem fin15Anchored_clause23803 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1282 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1282 Fin15AnchoredAtom3658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05260
  ] at hbad
  tauto

theorem fin15Anchored_clause23804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3658 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom3658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05260
  ] at hbad
  tauto

theorem fin15Anchored_clause23805 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3658 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1282 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom1137 Fin15AnchoredAtom1152
    Fin15AnchoredAtom1282 Fin15AnchoredAtom1447 Fin15AnchoredAtom3658 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05260
  ] at hbad
  tauto

theorem fin15Anchored_clause23806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom3659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09356
  ] at hbad
  tauto

theorem fin15Anchored_clause23807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3659 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom3659 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09356
  ] at hbad
  tauto

end ErdosSzekeres

end
