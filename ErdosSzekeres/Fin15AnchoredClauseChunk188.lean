module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 188. -/

theorem fin15Anchored_clause24064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom3736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20532
  ] at hbad
  tauto

theorem fin15Anchored_clause24065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom3736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20532
  ] at hbad
  tauto

theorem fin15Anchored_clause24066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom3736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20532
  ] at hbad
  tauto

theorem fin15Anchored_clause24067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1240 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1240 Fin15AnchoredAtom3736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20532
  ] at hbad
  tauto

theorem fin15Anchored_clause24068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3736 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom3736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20532
  ] at hbad
  tauto

theorem fin15Anchored_clause24069 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3736 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1240 chi ∧
      Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom1169 Fin15AnchoredAtom1204
    Fin15AnchoredAtom1240 Fin15AnchoredAtom1525 Fin15AnchoredAtom3736 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20532
  ] at hbad
  tauto

theorem fin15Anchored_clause24070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom3737 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24628
  ] at hbad
  tauto

theorem fin15Anchored_clause24071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom3737 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24628
  ] at hbad
  tauto

theorem fin15Anchored_clause24072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1205 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1205 Fin15AnchoredAtom3737 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24628
  ] at hbad
  tauto

theorem fin15Anchored_clause24073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1241 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1241 Fin15AnchoredAtom3737 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24628
  ] at hbad
  tauto

theorem fin15Anchored_clause24074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3737 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom3737 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24628
  ] at hbad
  tauto

theorem fin15Anchored_clause24075 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3737 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1205 chi ∧
      Fin15AnchoredAtom1241 chi ∧
      Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom1169 Fin15AnchoredAtom1205
    Fin15AnchoredAtom1241 Fin15AnchoredAtom1526 Fin15AnchoredAtom3737 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24628
  ] at hbad
  tauto

theorem fin15Anchored_clause24076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3738 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom3738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00468
  ] at hbad
  tauto

theorem fin15Anchored_clause24077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3738 chi ∧
      ¬Fin15AnchoredAtom1242 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1242 Fin15AnchoredAtom3738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00468
  ] at hbad
  tauto

theorem fin15Anchored_clause24078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3738 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom3738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00468
  ] at hbad
  tauto

theorem fin15Anchored_clause24079 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3738 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1171 chi ∧
      Fin15AnchoredAtom1178 chi ∧
      Fin15AnchoredAtom1242 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom1171 Fin15AnchoredAtom1178
    Fin15AnchoredAtom1242 Fin15AnchoredAtom1527 Fin15AnchoredAtom3738 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00468
  ] at hbad
  tauto

theorem fin15Anchored_clause24080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom3739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00724
  ] at hbad
  tauto

theorem fin15Anchored_clause24081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom3739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00724
  ] at hbad
  tauto

theorem fin15Anchored_clause24082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom3739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00724
  ] at hbad
  tauto

theorem fin15Anchored_clause24083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1243 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1243 Fin15AnchoredAtom3739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00724
  ] at hbad
  tauto

theorem fin15Anchored_clause24084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3739 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom3739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00724
  ] at hbad
  tauto

theorem fin15Anchored_clause24085 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3739 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1243 chi ∧
      Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom1172 Fin15AnchoredAtom1179
    Fin15AnchoredAtom1243 Fin15AnchoredAtom1528 Fin15AnchoredAtom3739 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00724
  ] at hbad
  tauto

theorem fin15Anchored_clause24086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom3740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01236
  ] at hbad
  tauto

theorem fin15Anchored_clause24087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom3740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01236
  ] at hbad
  tauto

theorem fin15Anchored_clause24088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom3740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01236
  ] at hbad
  tauto

theorem fin15Anchored_clause24089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1244 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1244 Fin15AnchoredAtom3740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01236
  ] at hbad
  tauto

theorem fin15Anchored_clause24090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3740 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom3740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01236
  ] at hbad
  tauto

theorem fin15Anchored_clause24091 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3740 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1244 chi ∧
      Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom1173 Fin15AnchoredAtom1180
    Fin15AnchoredAtom1244 Fin15AnchoredAtom1529 Fin15AnchoredAtom3740 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01236
  ] at hbad
  tauto

theorem fin15Anchored_clause24092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom3741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02260
  ] at hbad
  tauto

theorem fin15Anchored_clause24093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom1245 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1245 Fin15AnchoredAtom3741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02260
  ] at hbad
  tauto

theorem fin15Anchored_clause24094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3741 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1530 Fin15AnchoredAtom3741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02260
  ] at hbad
  tauto

theorem fin15Anchored_clause24095 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3741 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1174 chi ∧
      Fin15AnchoredAtom1181 chi ∧
      Fin15AnchoredAtom1245 chi ∧
      Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom1174 Fin15AnchoredAtom1181
    Fin15AnchoredAtom1245 Fin15AnchoredAtom1530 Fin15AnchoredAtom3741 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02260
  ] at hbad
  tauto

theorem fin15Anchored_clause24096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom3742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04308
  ] at hbad
  tauto

theorem fin15Anchored_clause24097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom3742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04308
  ] at hbad
  tauto

theorem fin15Anchored_clause24098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom3742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04308
  ] at hbad
  tauto

theorem fin15Anchored_clause24099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1246 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1246 Fin15AnchoredAtom3742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04308
  ] at hbad
  tauto

theorem fin15Anchored_clause24100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3742 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom3742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04308
  ] at hbad
  tauto

theorem fin15Anchored_clause24101 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3742 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1246 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom1175 Fin15AnchoredAtom1182
    Fin15AnchoredAtom1246 Fin15AnchoredAtom1531 Fin15AnchoredAtom3742 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04308
  ] at hbad
  tauto

theorem fin15Anchored_clause24102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom3743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08404
  ] at hbad
  tauto

theorem fin15Anchored_clause24103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom3743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08404
  ] at hbad
  tauto

theorem fin15Anchored_clause24104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom3743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08404
  ] at hbad
  tauto

theorem fin15Anchored_clause24105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1247 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1247 Fin15AnchoredAtom3743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08404
  ] at hbad
  tauto

theorem fin15Anchored_clause24106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3743 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom3743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08404
  ] at hbad
  tauto

theorem fin15Anchored_clause24107 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3743 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1247 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom1176 Fin15AnchoredAtom1183
    Fin15AnchoredAtom1247 Fin15AnchoredAtom1532 Fin15AnchoredAtom3743 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08404
  ] at hbad
  tauto

theorem fin15Anchored_clause24108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom3744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16596
  ] at hbad
  tauto

theorem fin15Anchored_clause24109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom3744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16596
  ] at hbad
  tauto

theorem fin15Anchored_clause24110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom3744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16596
  ] at hbad
  tauto

theorem fin15Anchored_clause24111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1248 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1248 Fin15AnchoredAtom3744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16596
  ] at hbad
  tauto

theorem fin15Anchored_clause24112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3744 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom3744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16596
  ] at hbad
  tauto

theorem fin15Anchored_clause24113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3744 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1248 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom1177 Fin15AnchoredAtom1184
    Fin15AnchoredAtom1248 Fin15AnchoredAtom1533 Fin15AnchoredAtom3744 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16596
  ] at hbad
  tauto

theorem fin15Anchored_clause24114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3745 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom3745 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00852
  ] at hbad
  tauto

theorem fin15Anchored_clause24115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3745 chi ∧
      ¬Fin15AnchoredAtom1249 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1249 Fin15AnchoredAtom3745 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00852
  ] at hbad
  tauto

theorem fin15Anchored_clause24116 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3745 chi ∧
      Fin15AnchoredAtom1171 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1185 chi ∧
      Fin15AnchoredAtom1249 chi ∧
      Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1171 Fin15AnchoredAtom1172 Fin15AnchoredAtom1185
    Fin15AnchoredAtom1249 Fin15AnchoredAtom1534 Fin15AnchoredAtom3745 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00852
  ] at hbad
  tauto

theorem fin15Anchored_clause24117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3746 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom3746 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01364
  ] at hbad
  tauto

theorem fin15Anchored_clause24118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3748 chi ∧
      ¬Fin15AnchoredAtom1171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1171 Fin15AnchoredAtom3748 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04436
  ] at hbad
  tauto

theorem fin15Anchored_clause24119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3749 chi ∧
      ¬Fin15AnchoredAtom1171 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1171 Fin15AnchoredAtom3749 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08532
  ] at hbad
  tauto

theorem fin15Anchored_clause24120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3749 chi ∧
      ¬Fin15AnchoredAtom1253 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1253 Fin15AnchoredAtom3749 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08532
  ] at hbad
  tauto

theorem fin15Anchored_clause24121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3750 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom3750 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16724
  ] at hbad
  tauto

theorem fin15Anchored_clause24122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom3751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01620
  ] at hbad
  tauto

theorem fin15Anchored_clause24123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom3751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01620
  ] at hbad
  tauto

theorem fin15Anchored_clause24124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom3751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01620
  ] at hbad
  tauto

theorem fin15Anchored_clause24125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1255 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1255 Fin15AnchoredAtom3751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01620
  ] at hbad
  tauto

theorem fin15Anchored_clause24126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3751 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom3751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01620
  ] at hbad
  tauto

theorem fin15Anchored_clause24127 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3751 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1255 chi ∧
      Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom1173 Fin15AnchoredAtom1191
    Fin15AnchoredAtom1255 Fin15AnchoredAtom1540 Fin15AnchoredAtom3751 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01620
  ] at hbad
  tauto

theorem fin15Anchored_clause24128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom3752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02644
  ] at hbad
  tauto

theorem fin15Anchored_clause24129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3752 chi ∧
      ¬Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1541 Fin15AnchoredAtom3752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02644
  ] at hbad
  tauto

theorem fin15Anchored_clause24130 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3752 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1174 chi ∧
      Fin15AnchoredAtom1192 chi ∧
      Fin15AnchoredAtom1256 chi ∧
      Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom1174 Fin15AnchoredAtom1192
    Fin15AnchoredAtom1256 Fin15AnchoredAtom1541 Fin15AnchoredAtom3752 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02644
  ] at hbad
  tauto

theorem fin15Anchored_clause24131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom3753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04692
  ] at hbad
  tauto

theorem fin15Anchored_clause24132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom3753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04692
  ] at hbad
  tauto

theorem fin15Anchored_clause24133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom3753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04692
  ] at hbad
  tauto

theorem fin15Anchored_clause24134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1257 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1257 Fin15AnchoredAtom3753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04692
  ] at hbad
  tauto

theorem fin15Anchored_clause24135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3753 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom3753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04692
  ] at hbad
  tauto

theorem fin15Anchored_clause24136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3753 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1257 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom1175 Fin15AnchoredAtom1193
    Fin15AnchoredAtom1257 Fin15AnchoredAtom1542 Fin15AnchoredAtom3753 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04692
  ] at hbad
  tauto

theorem fin15Anchored_clause24137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom3754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08788
  ] at hbad
  tauto

theorem fin15Anchored_clause24138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom3754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08788
  ] at hbad
  tauto

theorem fin15Anchored_clause24139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom3754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08788
  ] at hbad
  tauto

theorem fin15Anchored_clause24140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1258 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1258 Fin15AnchoredAtom3754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08788
  ] at hbad
  tauto

theorem fin15Anchored_clause24141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3754 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom3754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08788
  ] at hbad
  tauto

theorem fin15Anchored_clause24142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3754 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1258 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom1176 Fin15AnchoredAtom1194
    Fin15AnchoredAtom1258 Fin15AnchoredAtom1543 Fin15AnchoredAtom3754 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08788
  ] at hbad
  tauto

theorem fin15Anchored_clause24143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom3755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16980
  ] at hbad
  tauto

theorem fin15Anchored_clause24144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom3755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16980
  ] at hbad
  tauto

theorem fin15Anchored_clause24145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom3755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16980
  ] at hbad
  tauto

theorem fin15Anchored_clause24146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1259 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1259 Fin15AnchoredAtom3755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16980
  ] at hbad
  tauto

theorem fin15Anchored_clause24147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3755 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom3755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16980
  ] at hbad
  tauto

theorem fin15Anchored_clause24148 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3755 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1259 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom1177 Fin15AnchoredAtom1195
    Fin15AnchoredAtom1259 Fin15AnchoredAtom1544 Fin15AnchoredAtom3755 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16980
  ] at hbad
  tauto

theorem fin15Anchored_clause24149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom3756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03156
  ] at hbad
  tauto

theorem fin15Anchored_clause24150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom1196 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1196 Fin15AnchoredAtom3756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03156
  ] at hbad
  tauto

theorem fin15Anchored_clause24151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom1260 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1260 Fin15AnchoredAtom3756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03156
  ] at hbad
  tauto

theorem fin15Anchored_clause24152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3756 chi ∧
      ¬Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1545 Fin15AnchoredAtom3756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03156
  ] at hbad
  tauto

theorem fin15Anchored_clause24153 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3756 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1174 chi ∧
      Fin15AnchoredAtom1196 chi ∧
      Fin15AnchoredAtom1260 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom1174 Fin15AnchoredAtom1196
    Fin15AnchoredAtom1260 Fin15AnchoredAtom1545 Fin15AnchoredAtom3756 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03156
  ] at hbad
  tauto

theorem fin15Anchored_clause24154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom3757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05204
  ] at hbad
  tauto

theorem fin15Anchored_clause24155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom3757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05204
  ] at hbad
  tauto

theorem fin15Anchored_clause24156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom3757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05204
  ] at hbad
  tauto

theorem fin15Anchored_clause24157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1261 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1261 Fin15AnchoredAtom3757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05204
  ] at hbad
  tauto

theorem fin15Anchored_clause24158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3757 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom3757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05204
  ] at hbad
  tauto

theorem fin15Anchored_clause24159 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3757 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1261 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom1175 Fin15AnchoredAtom1197
    Fin15AnchoredAtom1261 Fin15AnchoredAtom1546 Fin15AnchoredAtom3757 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05204
  ] at hbad
  tauto

theorem fin15Anchored_clause24160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom3758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09300
  ] at hbad
  tauto

theorem fin15Anchored_clause24161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom3758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09300
  ] at hbad
  tauto

theorem fin15Anchored_clause24162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom3758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09300
  ] at hbad
  tauto

theorem fin15Anchored_clause24163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1262 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1262 Fin15AnchoredAtom3758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09300
  ] at hbad
  tauto

theorem fin15Anchored_clause24164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3758 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom3758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09300
  ] at hbad
  tauto

theorem fin15Anchored_clause24165 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3758 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1262 chi ∧
      Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom1176 Fin15AnchoredAtom1198
    Fin15AnchoredAtom1262 Fin15AnchoredAtom1547 Fin15AnchoredAtom3758 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09300
  ] at hbad
  tauto

theorem fin15Anchored_clause24166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom3759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17492
  ] at hbad
  tauto

theorem fin15Anchored_clause24167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom3759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17492
  ] at hbad
  tauto

theorem fin15Anchored_clause24168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom3759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17492
  ] at hbad
  tauto

theorem fin15Anchored_clause24169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1263 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1263 Fin15AnchoredAtom3759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17492
  ] at hbad
  tauto

theorem fin15Anchored_clause24170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3759 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom3759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17492
  ] at hbad
  tauto

theorem fin15Anchored_clause24171 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3759 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1263 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom1177 Fin15AnchoredAtom1199
    Fin15AnchoredAtom1263 Fin15AnchoredAtom1548 Fin15AnchoredAtom3759 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17492
  ] at hbad
  tauto

theorem fin15Anchored_clause24172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1174 Fin15AnchoredAtom3760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06228
  ] at hbad
  tauto

theorem fin15Anchored_clause24173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom3760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06228
  ] at hbad
  tauto

theorem fin15Anchored_clause24174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1200 Fin15AnchoredAtom3760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06228
  ] at hbad
  tauto

theorem fin15Anchored_clause24175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1264 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1264 Fin15AnchoredAtom3760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06228
  ] at hbad
  tauto

theorem fin15Anchored_clause24176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3760 chi ∧
      ¬Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1549 Fin15AnchoredAtom3760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06228
  ] at hbad
  tauto

theorem fin15Anchored_clause24177 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3760 chi ∧
      Fin15AnchoredAtom1174 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1200 chi ∧
      Fin15AnchoredAtom1264 chi ∧
      Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1174 Fin15AnchoredAtom1175 Fin15AnchoredAtom1200
    Fin15AnchoredAtom1264 Fin15AnchoredAtom1549 Fin15AnchoredAtom3760 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06228
  ] at hbad
  tauto

theorem fin15Anchored_clause24178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3761 chi ∧
      ¬Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1550 Fin15AnchoredAtom3761 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10324
  ] at hbad
  tauto

theorem fin15Anchored_clause24179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3762 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom3762 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18516
  ] at hbad
  tauto

theorem fin15Anchored_clause24180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom3763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12372
  ] at hbad
  tauto

theorem fin15Anchored_clause24181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom3763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12372
  ] at hbad
  tauto

theorem fin15Anchored_clause24182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom3763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12372
  ] at hbad
  tauto

theorem fin15Anchored_clause24183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1267 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1267 Fin15AnchoredAtom3763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12372
  ] at hbad
  tauto

theorem fin15Anchored_clause24184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3763 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom3763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12372
  ] at hbad
  tauto

theorem fin15Anchored_clause24185 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3763 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1267 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom1176 Fin15AnchoredAtom1203
    Fin15AnchoredAtom1267 Fin15AnchoredAtom1552 Fin15AnchoredAtom3763 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12372
  ] at hbad
  tauto

theorem fin15Anchored_clause24186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom3764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20564
  ] at hbad
  tauto

theorem fin15Anchored_clause24187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom3764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20564
  ] at hbad
  tauto

theorem fin15Anchored_clause24188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1204 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1204 Fin15AnchoredAtom3764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20564
  ] at hbad
  tauto

theorem fin15Anchored_clause24189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1268 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1268 Fin15AnchoredAtom3764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20564
  ] at hbad
  tauto

theorem fin15Anchored_clause24190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3764 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom3764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20564
  ] at hbad
  tauto

theorem fin15Anchored_clause24191 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3764 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1204 chi ∧
      Fin15AnchoredAtom1268 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom1177 Fin15AnchoredAtom1204
    Fin15AnchoredAtom1268 Fin15AnchoredAtom1553 Fin15AnchoredAtom3764 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20564
  ] at hbad
  tauto

end ErdosSzekeres

end
