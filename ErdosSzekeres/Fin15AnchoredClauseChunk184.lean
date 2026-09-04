module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 184. -/

theorem fin15Anchored_clause23552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3594 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom3594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04268
  ] at hbad
  tauto

theorem fin15Anchored_clause23553 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3594 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom1122 Fin15AnchoredAtom1137
    Fin15AnchoredAtom1218 Fin15AnchoredAtom1383 Fin15AnchoredAtom3594 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04268
  ] at hbad
  tauto

theorem fin15Anchored_clause23554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom3595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08364
  ] at hbad
  tauto

theorem fin15Anchored_clause23555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom3595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08364
  ] at hbad
  tauto

theorem fin15Anchored_clause23556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom3595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08364
  ] at hbad
  tauto

theorem fin15Anchored_clause23557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom3595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08364
  ] at hbad
  tauto

theorem fin15Anchored_clause23558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3595 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom3595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08364
  ] at hbad
  tauto

theorem fin15Anchored_clause23559 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3595 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom1123 Fin15AnchoredAtom1138
    Fin15AnchoredAtom1219 Fin15AnchoredAtom1384 Fin15AnchoredAtom3595 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08364
  ] at hbad
  tauto

theorem fin15Anchored_clause23560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom3596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16556
  ] at hbad
  tauto

theorem fin15Anchored_clause23561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1124 Fin15AnchoredAtom3596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16556
  ] at hbad
  tauto

theorem fin15Anchored_clause23562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom3596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16556
  ] at hbad
  tauto

theorem fin15Anchored_clause23563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom3596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16556
  ] at hbad
  tauto

theorem fin15Anchored_clause23564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3596 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom3596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16556
  ] at hbad
  tauto

theorem fin15Anchored_clause23565 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3596 chi ∧
      Fin15AnchoredAtom1117 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1139 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom1124 Fin15AnchoredAtom1139
    Fin15AnchoredAtom1220 Fin15AnchoredAtom1385 Fin15AnchoredAtom3596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16556
  ] at hbad
  tauto

theorem fin15Anchored_clause23566 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3597 chi ∧
      Fin15AnchoredAtom1118 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1140 chi ∧
      Fin15AnchoredAtom1221 chi ∧
      Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1118 Fin15AnchoredAtom1119 Fin15AnchoredAtom1140
    Fin15AnchoredAtom1221 Fin15AnchoredAtom1386 Fin15AnchoredAtom3597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00812
  ] at hbad
  tauto

theorem fin15Anchored_clause23567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3598 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom3598 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01324
  ] at hbad
  tauto

theorem fin15Anchored_clause23568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3598 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom3598 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01324
  ] at hbad
  tauto

theorem fin15Anchored_clause23569 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3598 chi ∧
      Fin15AnchoredAtom1118 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1141 chi ∧
      Fin15AnchoredAtom1222 chi ∧
      Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1118 Fin15AnchoredAtom1120 Fin15AnchoredAtom1141
    Fin15AnchoredAtom1222 Fin15AnchoredAtom1387 Fin15AnchoredAtom3598 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01324
  ] at hbad
  tauto

theorem fin15Anchored_clause23570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3600 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom3600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04396
  ] at hbad
  tauto

theorem fin15Anchored_clause23571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3601 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom3601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08492
  ] at hbad
  tauto

theorem fin15Anchored_clause23572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3601 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom3601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08492
  ] at hbad
  tauto

theorem fin15Anchored_clause23573 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3602 chi ∧
      Fin15AnchoredAtom1118 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1145 chi ∧
      Fin15AnchoredAtom1226 chi ∧
      Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1118 Fin15AnchoredAtom1124 Fin15AnchoredAtom1145
    Fin15AnchoredAtom1226 Fin15AnchoredAtom1391 Fin15AnchoredAtom3602 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16684
  ] at hbad
  tauto

theorem fin15Anchored_clause23574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom3603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01580
  ] at hbad
  tauto

theorem fin15Anchored_clause23575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom3603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01580
  ] at hbad
  tauto

theorem fin15Anchored_clause23576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom3603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01580
  ] at hbad
  tauto

theorem fin15Anchored_clause23577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom3603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01580
  ] at hbad
  tauto

theorem fin15Anchored_clause23578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3603 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom3603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01580
  ] at hbad
  tauto

theorem fin15Anchored_clause23579 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3603 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1146 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom1120 Fin15AnchoredAtom1146
    Fin15AnchoredAtom1227 Fin15AnchoredAtom1392 Fin15AnchoredAtom3603 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01580
  ] at hbad
  tauto

theorem fin15Anchored_clause23580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom3604 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02604
  ] at hbad
  tauto

theorem fin15Anchored_clause23581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom1147 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1147 Fin15AnchoredAtom3604 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02604
  ] at hbad
  tauto

theorem fin15Anchored_clause23582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3604 chi ∧
      ¬Fin15AnchoredAtom1228 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1228 Fin15AnchoredAtom3604 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02604
  ] at hbad
  tauto

theorem fin15Anchored_clause23583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom3605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04652
  ] at hbad
  tauto

theorem fin15Anchored_clause23584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom3605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04652
  ] at hbad
  tauto

theorem fin15Anchored_clause23585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom3605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04652
  ] at hbad
  tauto

theorem fin15Anchored_clause23586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom3605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04652
  ] at hbad
  tauto

theorem fin15Anchored_clause23587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3605 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom3605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04652
  ] at hbad
  tauto

theorem fin15Anchored_clause23588 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3605 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1148 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom1122 Fin15AnchoredAtom1148
    Fin15AnchoredAtom1229 Fin15AnchoredAtom1394 Fin15AnchoredAtom3605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04652
  ] at hbad
  tauto

theorem fin15Anchored_clause23589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom3606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08748
  ] at hbad
  tauto

theorem fin15Anchored_clause23590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom3606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08748
  ] at hbad
  tauto

theorem fin15Anchored_clause23591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom3606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08748
  ] at hbad
  tauto

theorem fin15Anchored_clause23592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom3606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08748
  ] at hbad
  tauto

theorem fin15Anchored_clause23593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3606 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom3606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08748
  ] at hbad
  tauto

theorem fin15Anchored_clause23594 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3606 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1149 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom1123 Fin15AnchoredAtom1149
    Fin15AnchoredAtom1230 Fin15AnchoredAtom1395 Fin15AnchoredAtom3606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08748
  ] at hbad
  tauto

theorem fin15Anchored_clause23595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom3607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16940
  ] at hbad
  tauto

theorem fin15Anchored_clause23596 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1124 Fin15AnchoredAtom3607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16940
  ] at hbad
  tauto

theorem fin15Anchored_clause23597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom3607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16940
  ] at hbad
  tauto

theorem fin15Anchored_clause23598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1231 Fin15AnchoredAtom3607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16940
  ] at hbad
  tauto

theorem fin15Anchored_clause23599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3607 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom3607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16940
  ] at hbad
  tauto

theorem fin15Anchored_clause23600 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3607 chi ∧
      Fin15AnchoredAtom1119 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1150 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom1124 Fin15AnchoredAtom1150
    Fin15AnchoredAtom1231 Fin15AnchoredAtom1396 Fin15AnchoredAtom3607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16940
  ] at hbad
  tauto

theorem fin15Anchored_clause23601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom3608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03116
  ] at hbad
  tauto

theorem fin15Anchored_clause23602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1121 Fin15AnchoredAtom3608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03116
  ] at hbad
  tauto

theorem fin15Anchored_clause23603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1151 Fin15AnchoredAtom3608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03116
  ] at hbad
  tauto

theorem fin15Anchored_clause23604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1232 Fin15AnchoredAtom3608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03116
  ] at hbad
  tauto

theorem fin15Anchored_clause23605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3608 chi ∧
      ¬Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1397 Fin15AnchoredAtom3608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03116
  ] at hbad
  tauto

theorem fin15Anchored_clause23606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3608 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1121 chi ∧
      Fin15AnchoredAtom1151 chi ∧
      Fin15AnchoredAtom1232 chi ∧
      Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom1121 Fin15AnchoredAtom1151
    Fin15AnchoredAtom1232 Fin15AnchoredAtom1397 Fin15AnchoredAtom3608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03116
  ] at hbad
  tauto

theorem fin15Anchored_clause23607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom3609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05164
  ] at hbad
  tauto

theorem fin15Anchored_clause23608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom3609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05164
  ] at hbad
  tauto

theorem fin15Anchored_clause23609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom3609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05164
  ] at hbad
  tauto

theorem fin15Anchored_clause23610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom3609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05164
  ] at hbad
  tauto

theorem fin15Anchored_clause23611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3609 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom3609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05164
  ] at hbad
  tauto

theorem fin15Anchored_clause23612 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3609 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1152 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom1122 Fin15AnchoredAtom1152
    Fin15AnchoredAtom1233 Fin15AnchoredAtom1398 Fin15AnchoredAtom3609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05164
  ] at hbad
  tauto

theorem fin15Anchored_clause23613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom3610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09260
  ] at hbad
  tauto

theorem fin15Anchored_clause23614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom3610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09260
  ] at hbad
  tauto

theorem fin15Anchored_clause23615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom3610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09260
  ] at hbad
  tauto

theorem fin15Anchored_clause23616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom3610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09260
  ] at hbad
  tauto

theorem fin15Anchored_clause23617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3610 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom3610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09260
  ] at hbad
  tauto

theorem fin15Anchored_clause23618 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3610 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1153 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom1123 Fin15AnchoredAtom1153
    Fin15AnchoredAtom1234 Fin15AnchoredAtom1399 Fin15AnchoredAtom3610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09260
  ] at hbad
  tauto

theorem fin15Anchored_clause23619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom3611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17452
  ] at hbad
  tauto

theorem fin15Anchored_clause23620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1124 Fin15AnchoredAtom3611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17452
  ] at hbad
  tauto

theorem fin15Anchored_clause23621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1154 Fin15AnchoredAtom3611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17452
  ] at hbad
  tauto

theorem fin15Anchored_clause23622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1235 Fin15AnchoredAtom3611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17452
  ] at hbad
  tauto

theorem fin15Anchored_clause23623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3611 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom3611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17452
  ] at hbad
  tauto

theorem fin15Anchored_clause23624 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3611 chi ∧
      Fin15AnchoredAtom1120 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1154 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom1124 Fin15AnchoredAtom1154
    Fin15AnchoredAtom1235 Fin15AnchoredAtom1400 Fin15AnchoredAtom3611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17452
  ] at hbad
  tauto

theorem fin15Anchored_clause23625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3612 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom3612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06188
  ] at hbad
  tauto

theorem fin15Anchored_clause23626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3612 chi ∧
      ¬Fin15AnchoredAtom1401 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1401 Fin15AnchoredAtom3612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06188
  ] at hbad
  tauto

theorem fin15Anchored_clause23627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3613 chi ∧
      ¬Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1121 Fin15AnchoredAtom3613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10284
  ] at hbad
  tauto

theorem fin15Anchored_clause23628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3613 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom3613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10284
  ] at hbad
  tauto

theorem fin15Anchored_clause23629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3613 chi ∧
      ¬Fin15AnchoredAtom1402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1402 Fin15AnchoredAtom3613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10284
  ] at hbad
  tauto

theorem fin15Anchored_clause23630 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3613 chi ∧
      Fin15AnchoredAtom1121 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1156 chi ∧
      Fin15AnchoredAtom1237 chi ∧
      Fin15AnchoredAtom1402 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1121 Fin15AnchoredAtom1123 Fin15AnchoredAtom1156
    Fin15AnchoredAtom1237 Fin15AnchoredAtom1402 Fin15AnchoredAtom3613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10284
  ] at hbad
  tauto

theorem fin15Anchored_clause23631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3614 chi ∧
      ¬Fin15AnchoredAtom1238 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1238 Fin15AnchoredAtom3614 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18476
  ] at hbad
  tauto

theorem fin15Anchored_clause23632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom3615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12332
  ] at hbad
  tauto

theorem fin15Anchored_clause23633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom3615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12332
  ] at hbad
  tauto

theorem fin15Anchored_clause23634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom3615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12332
  ] at hbad
  tauto

theorem fin15Anchored_clause23635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom3615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12332
  ] at hbad
  tauto

theorem fin15Anchored_clause23636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3615 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom3615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12332
  ] at hbad
  tauto

theorem fin15Anchored_clause23637 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3615 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom1123 Fin15AnchoredAtom1158
    Fin15AnchoredAtom1239 Fin15AnchoredAtom1404 Fin15AnchoredAtom3615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12332
  ] at hbad
  tauto

theorem fin15Anchored_clause23638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom3616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20524
  ] at hbad
  tauto

theorem fin15Anchored_clause23639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1124 Fin15AnchoredAtom3616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20524
  ] at hbad
  tauto

theorem fin15Anchored_clause23640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1159 Fin15AnchoredAtom3616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20524
  ] at hbad
  tauto

theorem fin15Anchored_clause23641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1240 Fin15AnchoredAtom3616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20524
  ] at hbad
  tauto

theorem fin15Anchored_clause23642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3616 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom3616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20524
  ] at hbad
  tauto

theorem fin15Anchored_clause23643 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3616 chi ∧
      Fin15AnchoredAtom1122 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom1124 Fin15AnchoredAtom1159
    Fin15AnchoredAtom1240 Fin15AnchoredAtom1405 Fin15AnchoredAtom3616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20524
  ] at hbad
  tauto

theorem fin15Anchored_clause23644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom3617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24620
  ] at hbad
  tauto

theorem fin15Anchored_clause23645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1124 Fin15AnchoredAtom3617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24620
  ] at hbad
  tauto

theorem fin15Anchored_clause23646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1160 Fin15AnchoredAtom3617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24620
  ] at hbad
  tauto

theorem fin15Anchored_clause23647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom3617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24620
  ] at hbad
  tauto

theorem fin15Anchored_clause23648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3617 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom3617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24620
  ] at hbad
  tauto

theorem fin15Anchored_clause23649 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3617 chi ∧
      Fin15AnchoredAtom1123 chi ∧
      Fin15AnchoredAtom1124 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom1124 Fin15AnchoredAtom1160
    Fin15AnchoredAtom1241 Fin15AnchoredAtom1406 Fin15AnchoredAtom3617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24620
  ] at hbad
  tauto

theorem fin15Anchored_clause23650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3618 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom3618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00460
  ] at hbad
  tauto

theorem fin15Anchored_clause23651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom3619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00716
  ] at hbad
  tauto

theorem fin15Anchored_clause23652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom3619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00716
  ] at hbad
  tauto

theorem fin15Anchored_clause23653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom3619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00716
  ] at hbad
  tauto

theorem fin15Anchored_clause23654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom3619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00716
  ] at hbad
  tauto

theorem fin15Anchored_clause23655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3619 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom3619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00716
  ] at hbad
  tauto

theorem fin15Anchored_clause23656 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3619 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1127 chi ∧
      Fin15AnchoredAtom1134 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom1127 Fin15AnchoredAtom1134
    Fin15AnchoredAtom1243 Fin15AnchoredAtom1408 Fin15AnchoredAtom3619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00716
  ] at hbad
  tauto

theorem fin15Anchored_clause23657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom3620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01228
  ] at hbad
  tauto

theorem fin15Anchored_clause23658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom3620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01228
  ] at hbad
  tauto

theorem fin15Anchored_clause23659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom3620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01228
  ] at hbad
  tauto

theorem fin15Anchored_clause23660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom3620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01228
  ] at hbad
  tauto

theorem fin15Anchored_clause23661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3620 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom3620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01228
  ] at hbad
  tauto

theorem fin15Anchored_clause23662 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3620 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1128 chi ∧
      Fin15AnchoredAtom1135 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom1128 Fin15AnchoredAtom1135
    Fin15AnchoredAtom1244 Fin15AnchoredAtom1409 Fin15AnchoredAtom3620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01228
  ] at hbad
  tauto

theorem fin15Anchored_clause23663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3621 chi ∧
      ¬Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1245 Fin15AnchoredAtom3621 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02252
  ] at hbad
  tauto

theorem fin15Anchored_clause23664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3621 chi ∧
      ¬Fin15AnchoredAtom1410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1410 Fin15AnchoredAtom3621 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02252
  ] at hbad
  tauto

theorem fin15Anchored_clause23665 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3621 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1129 chi ∧
      Fin15AnchoredAtom1136 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom1129 Fin15AnchoredAtom1136
    Fin15AnchoredAtom1245 Fin15AnchoredAtom1410 Fin15AnchoredAtom3621 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02252
  ] at hbad
  tauto

theorem fin15Anchored_clause23666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom3622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04300
  ] at hbad
  tauto

theorem fin15Anchored_clause23667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom3622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04300
  ] at hbad
  tauto

theorem fin15Anchored_clause23668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom3622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04300
  ] at hbad
  tauto

theorem fin15Anchored_clause23669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom3622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04300
  ] at hbad
  tauto

theorem fin15Anchored_clause23670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3622 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom3622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04300
  ] at hbad
  tauto

theorem fin15Anchored_clause23671 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3622 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1130 chi ∧
      Fin15AnchoredAtom1137 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom1130 Fin15AnchoredAtom1137
    Fin15AnchoredAtom1246 Fin15AnchoredAtom1411 Fin15AnchoredAtom3622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04300
  ] at hbad
  tauto

theorem fin15Anchored_clause23672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom3623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08396
  ] at hbad
  tauto

theorem fin15Anchored_clause23673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom3623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08396
  ] at hbad
  tauto

theorem fin15Anchored_clause23674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom3623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08396
  ] at hbad
  tauto

theorem fin15Anchored_clause23675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom3623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08396
  ] at hbad
  tauto

theorem fin15Anchored_clause23676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3623 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom3623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08396
  ] at hbad
  tauto

theorem fin15Anchored_clause23677 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3623 chi ∧
      Fin15AnchoredAtom1125 chi ∧
      Fin15AnchoredAtom1131 chi ∧
      Fin15AnchoredAtom1138 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom1131 Fin15AnchoredAtom1138
    Fin15AnchoredAtom1247 Fin15AnchoredAtom1412 Fin15AnchoredAtom3623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08396
  ] at hbad
  tauto

theorem fin15Anchored_clause23678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom3624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16588
  ] at hbad
  tauto

theorem fin15Anchored_clause23679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3624 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom3624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16588
  ] at hbad
  tauto

end ErdosSzekeres

end
