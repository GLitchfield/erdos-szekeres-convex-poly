module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 187. -/

theorem fin15Anchored_clause23936 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3701 chi ∧
      Fin15AnchoredAtom1158 chi ∧
      Fin15AnchoredAtom1159 chi ∧
      Fin15AnchoredAtom1160 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom1159 Fin15AnchoredAtom1160
    Fin15AnchoredAtom1325 Fin15AnchoredAtom1490 Fin15AnchoredAtom3701 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28684
  ] at hbad
  tauto

theorem fin15Anchored_clause23937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom3702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00244
  ] at hbad
  tauto

theorem fin15Anchored_clause23938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom3702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00244
  ] at hbad
  tauto

theorem fin15Anchored_clause23939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom3702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00244
  ] at hbad
  tauto

theorem fin15Anchored_clause23940 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1206 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1206 Fin15AnchoredAtom3702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00244
  ] at hbad
  tauto

theorem fin15Anchored_clause23941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3702 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom3702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00244
  ] at hbad
  tauto

theorem fin15Anchored_clause23942 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3702 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1170 chi ∧
      Fin15AnchoredAtom1206 chi ∧
      Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom1162 Fin15AnchoredAtom1170
    Fin15AnchoredAtom1206 Fin15AnchoredAtom1491 Fin15AnchoredAtom3702 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00244
  ] at hbad
  tauto

theorem fin15Anchored_clause23943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3703 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom3703 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00372
  ] at hbad
  tauto

theorem fin15Anchored_clause23944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom3704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00628
  ] at hbad
  tauto

theorem fin15Anchored_clause23945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom3704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00628
  ] at hbad
  tauto

theorem fin15Anchored_clause23946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom3704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00628
  ] at hbad
  tauto

theorem fin15Anchored_clause23947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1208 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1208 Fin15AnchoredAtom3704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00628
  ] at hbad
  tauto

theorem fin15Anchored_clause23948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3704 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom3704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00628
  ] at hbad
  tauto

theorem fin15Anchored_clause23949 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3704 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1172 chi ∧
      Fin15AnchoredAtom1208 chi ∧
      Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom1164 Fin15AnchoredAtom1172
    Fin15AnchoredAtom1208 Fin15AnchoredAtom1493 Fin15AnchoredAtom3704 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00628
  ] at hbad
  tauto

theorem fin15Anchored_clause23950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom3705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01140
  ] at hbad
  tauto

theorem fin15Anchored_clause23951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom3705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01140
  ] at hbad
  tauto

theorem fin15Anchored_clause23952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom3705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01140
  ] at hbad
  tauto

theorem fin15Anchored_clause23953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1209 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1209 Fin15AnchoredAtom3705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01140
  ] at hbad
  tauto

theorem fin15Anchored_clause23954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3705 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom3705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01140
  ] at hbad
  tauto

theorem fin15Anchored_clause23955 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3705 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1173 chi ∧
      Fin15AnchoredAtom1209 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom1165 Fin15AnchoredAtom1173
    Fin15AnchoredAtom1209 Fin15AnchoredAtom1494 Fin15AnchoredAtom3705 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01140
  ] at hbad
  tauto

theorem fin15Anchored_clause23956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom1210 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1210 Fin15AnchoredAtom3706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02164
  ] at hbad
  tauto

theorem fin15Anchored_clause23957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3706 chi ∧
      ¬Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1495 Fin15AnchoredAtom3706 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02164
  ] at hbad
  tauto

theorem fin15Anchored_clause23958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom3707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04212
  ] at hbad
  tauto

theorem fin15Anchored_clause23959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom3707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04212
  ] at hbad
  tauto

theorem fin15Anchored_clause23960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom3707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04212
  ] at hbad
  tauto

theorem fin15Anchored_clause23961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1211 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1211 Fin15AnchoredAtom3707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04212
  ] at hbad
  tauto

theorem fin15Anchored_clause23962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3707 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom3707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04212
  ] at hbad
  tauto

theorem fin15Anchored_clause23963 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3707 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1175 chi ∧
      Fin15AnchoredAtom1211 chi ∧
      Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom1167 Fin15AnchoredAtom1175
    Fin15AnchoredAtom1211 Fin15AnchoredAtom1496 Fin15AnchoredAtom3707 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04212
  ] at hbad
  tauto

theorem fin15Anchored_clause23964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom3708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08308
  ] at hbad
  tauto

theorem fin15Anchored_clause23965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom3708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08308
  ] at hbad
  tauto

theorem fin15Anchored_clause23966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom3708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08308
  ] at hbad
  tauto

theorem fin15Anchored_clause23967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1212 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1212 Fin15AnchoredAtom3708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08308
  ] at hbad
  tauto

theorem fin15Anchored_clause23968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3708 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom3708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08308
  ] at hbad
  tauto

theorem fin15Anchored_clause23969 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3708 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1176 chi ∧
      Fin15AnchoredAtom1212 chi ∧
      Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom1168 Fin15AnchoredAtom1176
    Fin15AnchoredAtom1212 Fin15AnchoredAtom1497 Fin15AnchoredAtom3708 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08308
  ] at hbad
  tauto

theorem fin15Anchored_clause23970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom3709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16500
  ] at hbad
  tauto

theorem fin15Anchored_clause23971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom3709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16500
  ] at hbad
  tauto

theorem fin15Anchored_clause23972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom3709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16500
  ] at hbad
  tauto

theorem fin15Anchored_clause23973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1213 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1213 Fin15AnchoredAtom3709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16500
  ] at hbad
  tauto

theorem fin15Anchored_clause23974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3709 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom3709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16500
  ] at hbad
  tauto

theorem fin15Anchored_clause23975 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3709 chi ∧
      Fin15AnchoredAtom1161 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1177 chi ∧
      Fin15AnchoredAtom1213 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom1169 Fin15AnchoredAtom1177
    Fin15AnchoredAtom1213 Fin15AnchoredAtom1498 Fin15AnchoredAtom3709 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16500
  ] at hbad
  tauto

theorem fin15Anchored_clause23976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom3711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00692
  ] at hbad
  tauto

theorem fin15Anchored_clause23977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom3711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00692
  ] at hbad
  tauto

theorem fin15Anchored_clause23978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom3711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00692
  ] at hbad
  tauto

theorem fin15Anchored_clause23979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1215 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1215 Fin15AnchoredAtom3711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00692
  ] at hbad
  tauto

theorem fin15Anchored_clause23980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3711 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom3711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00692
  ] at hbad
  tauto

theorem fin15Anchored_clause23981 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3711 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1179 chi ∧
      Fin15AnchoredAtom1215 chi ∧
      Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom1164 Fin15AnchoredAtom1179
    Fin15AnchoredAtom1215 Fin15AnchoredAtom1500 Fin15AnchoredAtom3711 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00692
  ] at hbad
  tauto

theorem fin15Anchored_clause23982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom3712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01204
  ] at hbad
  tauto

theorem fin15Anchored_clause23983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom3712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01204
  ] at hbad
  tauto

theorem fin15Anchored_clause23984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom3712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01204
  ] at hbad
  tauto

theorem fin15Anchored_clause23985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1216 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1216 Fin15AnchoredAtom3712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01204
  ] at hbad
  tauto

theorem fin15Anchored_clause23986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3712 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom3712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01204
  ] at hbad
  tauto

theorem fin15Anchored_clause23987 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3712 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1180 chi ∧
      Fin15AnchoredAtom1216 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom1165 Fin15AnchoredAtom1180
    Fin15AnchoredAtom1216 Fin15AnchoredAtom1501 Fin15AnchoredAtom3712 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01204
  ] at hbad
  tauto

theorem fin15Anchored_clause23988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3713 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1502 Fin15AnchoredAtom3713 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02228
  ] at hbad
  tauto

theorem fin15Anchored_clause23989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom3714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04276
  ] at hbad
  tauto

theorem fin15Anchored_clause23990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom3714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04276
  ] at hbad
  tauto

theorem fin15Anchored_clause23991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom3714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04276
  ] at hbad
  tauto

theorem fin15Anchored_clause23992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1218 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1218 Fin15AnchoredAtom3714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04276
  ] at hbad
  tauto

theorem fin15Anchored_clause23993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3714 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom3714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04276
  ] at hbad
  tauto

theorem fin15Anchored_clause23994 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3714 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1182 chi ∧
      Fin15AnchoredAtom1218 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom1167 Fin15AnchoredAtom1182
    Fin15AnchoredAtom1218 Fin15AnchoredAtom1503 Fin15AnchoredAtom3714 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04276
  ] at hbad
  tauto

theorem fin15Anchored_clause23995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom3715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08372
  ] at hbad
  tauto

theorem fin15Anchored_clause23996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom3715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08372
  ] at hbad
  tauto

theorem fin15Anchored_clause23997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom3715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08372
  ] at hbad
  tauto

theorem fin15Anchored_clause23998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1219 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1219 Fin15AnchoredAtom3715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08372
  ] at hbad
  tauto

theorem fin15Anchored_clause23999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3715 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom3715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08372
  ] at hbad
  tauto

theorem fin15Anchored_clause24000 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3715 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1183 chi ∧
      Fin15AnchoredAtom1219 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom1168 Fin15AnchoredAtom1183
    Fin15AnchoredAtom1219 Fin15AnchoredAtom1504 Fin15AnchoredAtom3715 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08372
  ] at hbad
  tauto

theorem fin15Anchored_clause24001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom3716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16564
  ] at hbad
  tauto

theorem fin15Anchored_clause24002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom3716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16564
  ] at hbad
  tauto

theorem fin15Anchored_clause24003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom3716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16564
  ] at hbad
  tauto

theorem fin15Anchored_clause24004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1220 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1220 Fin15AnchoredAtom3716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16564
  ] at hbad
  tauto

theorem fin15Anchored_clause24005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3716 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom3716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16564
  ] at hbad
  tauto

theorem fin15Anchored_clause24006 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3716 chi ∧
      Fin15AnchoredAtom1162 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1184 chi ∧
      Fin15AnchoredAtom1220 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom1169 Fin15AnchoredAtom1184
    Fin15AnchoredAtom1220 Fin15AnchoredAtom1505 Fin15AnchoredAtom3716 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16564
  ] at hbad
  tauto

theorem fin15Anchored_clause24007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3721 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom3721 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08500
  ] at hbad
  tauto

theorem fin15Anchored_clause24008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom3723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01588
  ] at hbad
  tauto

theorem fin15Anchored_clause24009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom3723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01588
  ] at hbad
  tauto

theorem fin15Anchored_clause24010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom3723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01588
  ] at hbad
  tauto

theorem fin15Anchored_clause24011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1227 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1227 Fin15AnchoredAtom3723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01588
  ] at hbad
  tauto

theorem fin15Anchored_clause24012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3723 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom3723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01588
  ] at hbad
  tauto

theorem fin15Anchored_clause24013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3723 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1191 chi ∧
      Fin15AnchoredAtom1227 chi ∧
      Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom1165 Fin15AnchoredAtom1191
    Fin15AnchoredAtom1227 Fin15AnchoredAtom1512 Fin15AnchoredAtom3723 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01588
  ] at hbad
  tauto

theorem fin15Anchored_clause24014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom3724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02612
  ] at hbad
  tauto

theorem fin15Anchored_clause24015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3724 chi ∧
      ¬Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1513 Fin15AnchoredAtom3724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02612
  ] at hbad
  tauto

theorem fin15Anchored_clause24016 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3724 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1166 chi ∧
      Fin15AnchoredAtom1192 chi ∧
      Fin15AnchoredAtom1228 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom1166 Fin15AnchoredAtom1192
    Fin15AnchoredAtom1228 Fin15AnchoredAtom1513 Fin15AnchoredAtom3724 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02612
  ] at hbad
  tauto

theorem fin15Anchored_clause24017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom3725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04660
  ] at hbad
  tauto

theorem fin15Anchored_clause24018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom3725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04660
  ] at hbad
  tauto

theorem fin15Anchored_clause24019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom3725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04660
  ] at hbad
  tauto

theorem fin15Anchored_clause24020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1229 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1229 Fin15AnchoredAtom3725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04660
  ] at hbad
  tauto

theorem fin15Anchored_clause24021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3725 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom3725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04660
  ] at hbad
  tauto

theorem fin15Anchored_clause24022 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3725 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1193 chi ∧
      Fin15AnchoredAtom1229 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom1167 Fin15AnchoredAtom1193
    Fin15AnchoredAtom1229 Fin15AnchoredAtom1514 Fin15AnchoredAtom3725 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04660
  ] at hbad
  tauto

theorem fin15Anchored_clause24023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom3726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08756
  ] at hbad
  tauto

theorem fin15Anchored_clause24024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom3726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08756
  ] at hbad
  tauto

theorem fin15Anchored_clause24025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom3726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08756
  ] at hbad
  tauto

theorem fin15Anchored_clause24026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1230 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1230 Fin15AnchoredAtom3726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08756
  ] at hbad
  tauto

theorem fin15Anchored_clause24027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3726 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom3726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08756
  ] at hbad
  tauto

theorem fin15Anchored_clause24028 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3726 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1194 chi ∧
      Fin15AnchoredAtom1230 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom1168 Fin15AnchoredAtom1194
    Fin15AnchoredAtom1230 Fin15AnchoredAtom1515 Fin15AnchoredAtom3726 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08756
  ] at hbad
  tauto

theorem fin15Anchored_clause24029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom3727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16948
  ] at hbad
  tauto

theorem fin15Anchored_clause24030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom3727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16948
  ] at hbad
  tauto

theorem fin15Anchored_clause24031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom3727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16948
  ] at hbad
  tauto

theorem fin15Anchored_clause24032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1231 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1231 Fin15AnchoredAtom3727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16948
  ] at hbad
  tauto

theorem fin15Anchored_clause24033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3727 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom3727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16948
  ] at hbad
  tauto

theorem fin15Anchored_clause24034 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3727 chi ∧
      Fin15AnchoredAtom1164 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1195 chi ∧
      Fin15AnchoredAtom1231 chi ∧
      Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom1169 Fin15AnchoredAtom1195
    Fin15AnchoredAtom1231 Fin15AnchoredAtom1516 Fin15AnchoredAtom3727 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16948
  ] at hbad
  tauto

theorem fin15Anchored_clause24035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom3728 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03124
  ] at hbad
  tauto

theorem fin15Anchored_clause24036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3728 chi ∧
      ¬Fin15AnchoredAtom1232 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1232 Fin15AnchoredAtom3728 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03124
  ] at hbad
  tauto

theorem fin15Anchored_clause24037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom3729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05172
  ] at hbad
  tauto

theorem fin15Anchored_clause24038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom3729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05172
  ] at hbad
  tauto

theorem fin15Anchored_clause24039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom3729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05172
  ] at hbad
  tauto

theorem fin15Anchored_clause24040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1233 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1233 Fin15AnchoredAtom3729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05172
  ] at hbad
  tauto

theorem fin15Anchored_clause24041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3729 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom3729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05172
  ] at hbad
  tauto

theorem fin15Anchored_clause24042 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3729 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1197 chi ∧
      Fin15AnchoredAtom1233 chi ∧
      Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom1167 Fin15AnchoredAtom1197
    Fin15AnchoredAtom1233 Fin15AnchoredAtom1518 Fin15AnchoredAtom3729 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05172
  ] at hbad
  tauto

theorem fin15Anchored_clause24043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom3730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09268
  ] at hbad
  tauto

theorem fin15Anchored_clause24044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom3730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09268
  ] at hbad
  tauto

theorem fin15Anchored_clause24045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom3730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09268
  ] at hbad
  tauto

theorem fin15Anchored_clause24046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1234 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1234 Fin15AnchoredAtom3730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09268
  ] at hbad
  tauto

theorem fin15Anchored_clause24047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3730 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom3730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09268
  ] at hbad
  tauto

theorem fin15Anchored_clause24048 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3730 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1198 chi ∧
      Fin15AnchoredAtom1234 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom1168 Fin15AnchoredAtom1198
    Fin15AnchoredAtom1234 Fin15AnchoredAtom1519 Fin15AnchoredAtom3730 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09268
  ] at hbad
  tauto

theorem fin15Anchored_clause24049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom3731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17460
  ] at hbad
  tauto

theorem fin15Anchored_clause24050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom3731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17460
  ] at hbad
  tauto

theorem fin15Anchored_clause24051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom3731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17460
  ] at hbad
  tauto

theorem fin15Anchored_clause24052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1235 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1235 Fin15AnchoredAtom3731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17460
  ] at hbad
  tauto

theorem fin15Anchored_clause24053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3731 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom3731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17460
  ] at hbad
  tauto

theorem fin15Anchored_clause24054 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3731 chi ∧
      Fin15AnchoredAtom1165 chi ∧
      Fin15AnchoredAtom1169 chi ∧
      Fin15AnchoredAtom1199 chi ∧
      Fin15AnchoredAtom1235 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom1169 Fin15AnchoredAtom1199
    Fin15AnchoredAtom1235 Fin15AnchoredAtom1520 Fin15AnchoredAtom3731 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17460
  ] at hbad
  tauto

theorem fin15Anchored_clause24055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3732 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom3732 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06196
  ] at hbad
  tauto

theorem fin15Anchored_clause24056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3733 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom3733 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10292
  ] at hbad
  tauto

theorem fin15Anchored_clause24057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3734 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom3734 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18484
  ] at hbad
  tauto

theorem fin15Anchored_clause24058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom3735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12340
  ] at hbad
  tauto

theorem fin15Anchored_clause24059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom3735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12340
  ] at hbad
  tauto

theorem fin15Anchored_clause24060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1203 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1203 Fin15AnchoredAtom3735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12340
  ] at hbad
  tauto

theorem fin15Anchored_clause24061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1239 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1239 Fin15AnchoredAtom3735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12340
  ] at hbad
  tauto

theorem fin15Anchored_clause24062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3735 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom3735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12340
  ] at hbad
  tauto

theorem fin15Anchored_clause24063 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3735 chi ∧
      Fin15AnchoredAtom1167 chi ∧
      Fin15AnchoredAtom1168 chi ∧
      Fin15AnchoredAtom1203 chi ∧
      Fin15AnchoredAtom1239 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom1168 Fin15AnchoredAtom1203
    Fin15AnchoredAtom1239 Fin15AnchoredAtom1524 Fin15AnchoredAtom3735 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12340
  ] at hbad
  tauto

end ErdosSzekeres

end
