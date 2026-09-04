module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 195. -/

theorem fin15Anchored_clause24960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom4021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22020
  ] at hbad
  tauto

theorem fin15Anchored_clause24961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom4021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22020
  ] at hbad
  tauto

theorem fin15Anchored_clause24962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom4021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22020
  ] at hbad
  tauto

theorem fin15Anchored_clause24963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4021 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom4021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22020
  ] at hbad
  tauto

theorem fin15Anchored_clause24964 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4021 chi ∧
      Fin15AnchoredAtom1307 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1307 Fin15AnchoredAtom1309 Fin15AnchoredAtom1314
    Fin15AnchoredAtom1320 Fin15AnchoredAtom1810 Fin15AnchoredAtom4021 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22020
  ] at hbad
  tauto

theorem fin15Anchored_clause24965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1308 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom4022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26116
  ] at hbad
  tauto

theorem fin15Anchored_clause24966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1309 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1309 Fin15AnchoredAtom4022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26116
  ] at hbad
  tauto

theorem fin15Anchored_clause24967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1315 Fin15AnchoredAtom4022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26116
  ] at hbad
  tauto

theorem fin15Anchored_clause24968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom4022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26116
  ] at hbad
  tauto

theorem fin15Anchored_clause24969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4022 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom4022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26116
  ] at hbad
  tauto

theorem fin15Anchored_clause24970 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4022 chi ∧
      Fin15AnchoredAtom1308 chi ∧
      Fin15AnchoredAtom1309 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1308 Fin15AnchoredAtom1309 Fin15AnchoredAtom1315
    Fin15AnchoredAtom1321 Fin15AnchoredAtom1811 Fin15AnchoredAtom4022 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26116
  ] at hbad
  tauto

theorem fin15Anchored_clause24971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1310 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1310 Fin15AnchoredAtom4023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14852
  ] at hbad
  tauto

theorem fin15Anchored_clause24972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1311 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1311 Fin15AnchoredAtom4023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14852
  ] at hbad
  tauto

theorem fin15Anchored_clause24973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom4023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14852
  ] at hbad
  tauto

theorem fin15Anchored_clause24974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1322 Fin15AnchoredAtom4023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14852
  ] at hbad
  tauto

theorem fin15Anchored_clause24975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4023 chi ∧
      ¬Fin15AnchoredAtom1812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1812 Fin15AnchoredAtom4023 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14852
  ] at hbad
  tauto

theorem fin15Anchored_clause24976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4024 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom4024 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23044
  ] at hbad
  tauto

theorem fin15Anchored_clause24977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4025 chi ∧
      ¬Fin15AnchoredAtom1312 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1312 Fin15AnchoredAtom4025 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27140
  ] at hbad
  tauto

theorem fin15Anchored_clause24978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1313 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom4026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29188
  ] at hbad
  tauto

theorem fin15Anchored_clause24979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1314 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1314 Fin15AnchoredAtom4026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29188
  ] at hbad
  tauto

theorem fin15Anchored_clause24980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1315 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1315 Fin15AnchoredAtom4026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29188
  ] at hbad
  tauto

theorem fin15Anchored_clause24981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom4026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29188
  ] at hbad
  tauto

theorem fin15Anchored_clause24982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4026 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom4026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29188
  ] at hbad
  tauto

theorem fin15Anchored_clause24983 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4026 chi ∧
      Fin15AnchoredAtom1313 chi ∧
      Fin15AnchoredAtom1314 chi ∧
      Fin15AnchoredAtom1315 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1313 Fin15AnchoredAtom1314 Fin15AnchoredAtom1315
    Fin15AnchoredAtom1325 Fin15AnchoredAtom1815 Fin15AnchoredAtom4026 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29188
  ] at hbad
  tauto

theorem fin15Anchored_clause24984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4027 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom4027 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15364
  ] at hbad
  tauto

theorem fin15Anchored_clause24985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4027 chi ∧
      ¬Fin15AnchoredAtom1322 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1322 Fin15AnchoredAtom4027 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15364
  ] at hbad
  tauto

theorem fin15Anchored_clause24986 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4027 chi ∧
      Fin15AnchoredAtom1316 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1322 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1316 Fin15AnchoredAtom1317 Fin15AnchoredAtom1319
    Fin15AnchoredAtom1322 Fin15AnchoredAtom1816 Fin15AnchoredAtom4027 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15364
  ] at hbad
  tauto

theorem fin15Anchored_clause24987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4028 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom4028 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23556
  ] at hbad
  tauto

theorem fin15Anchored_clause24988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4029 chi ∧
      ¬Fin15AnchoredAtom1317 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1317 Fin15AnchoredAtom4029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27652
  ] at hbad
  tauto

theorem fin15Anchored_clause24989 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4029 chi ∧
      Fin15AnchoredAtom1317 chi ∧
      Fin15AnchoredAtom1318 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1324 chi ∧
      Fin15AnchoredAtom1818 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1317 Fin15AnchoredAtom1318 Fin15AnchoredAtom1321
    Fin15AnchoredAtom1324 Fin15AnchoredAtom1818 Fin15AnchoredAtom4029 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27652
  ] at hbad
  tauto

theorem fin15Anchored_clause24990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1319 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom4030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29700
  ] at hbad
  tauto

theorem fin15Anchored_clause24991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1320 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1320 Fin15AnchoredAtom4030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29700
  ] at hbad
  tauto

theorem fin15Anchored_clause24992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1321 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1321 Fin15AnchoredAtom4030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29700
  ] at hbad
  tauto

theorem fin15Anchored_clause24993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1325 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1325 Fin15AnchoredAtom4030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29700
  ] at hbad
  tauto

theorem fin15Anchored_clause24994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4030 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom4030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29700
  ] at hbad
  tauto

theorem fin15Anchored_clause24995 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4030 chi ∧
      Fin15AnchoredAtom1319 chi ∧
      Fin15AnchoredAtom1320 chi ∧
      Fin15AnchoredAtom1321 chi ∧
      Fin15AnchoredAtom1325 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1319 Fin15AnchoredAtom1320 Fin15AnchoredAtom1321
    Fin15AnchoredAtom1325 Fin15AnchoredAtom1819 Fin15AnchoredAtom4030 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29700
  ] at hbad
  tauto

theorem fin15Anchored_clause24996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4031 chi ∧
      ¬Fin15AnchoredAtom1323 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1323 Fin15AnchoredAtom4031 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask30724
  ] at hbad
  tauto

theorem fin15Anchored_clause24997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom4032 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00248
  ] at hbad
  tauto

theorem fin15Anchored_clause24998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom4032 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00248
  ] at hbad
  tauto

theorem fin15Anchored_clause24999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom4032 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00248
  ] at hbad
  tauto

theorem fin15Anchored_clause25000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom4032 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00248
  ] at hbad
  tauto

theorem fin15Anchored_clause25001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4032 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom4032 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00248
  ] at hbad
  tauto

theorem fin15Anchored_clause25002 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4032 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom1327 Fin15AnchoredAtom1335
    Fin15AnchoredAtom1371 Fin15AnchoredAtom1491 Fin15AnchoredAtom4032 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00248
  ] at hbad
  tauto

theorem fin15Anchored_clause25003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom4033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00376
  ] at hbad
  tauto

theorem fin15Anchored_clause25004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom4033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00376
  ] at hbad
  tauto

theorem fin15Anchored_clause25005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom4033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00376
  ] at hbad
  tauto

theorem fin15Anchored_clause25006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom4033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00376
  ] at hbad
  tauto

theorem fin15Anchored_clause25007 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4033 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom4033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00376
  ] at hbad
  tauto

theorem fin15Anchored_clause25008 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4033 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom1328 Fin15AnchoredAtom1336
    Fin15AnchoredAtom1372 Fin15AnchoredAtom1492 Fin15AnchoredAtom4033 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00376
  ] at hbad
  tauto

theorem fin15Anchored_clause25009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom4034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00632
  ] at hbad
  tauto

theorem fin15Anchored_clause25010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom4034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00632
  ] at hbad
  tauto

theorem fin15Anchored_clause25011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom4034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00632
  ] at hbad
  tauto

theorem fin15Anchored_clause25012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom4034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00632
  ] at hbad
  tauto

theorem fin15Anchored_clause25013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4034 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom4034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00632
  ] at hbad
  tauto

theorem fin15Anchored_clause25014 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4034 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom1329 Fin15AnchoredAtom1337
    Fin15AnchoredAtom1373 Fin15AnchoredAtom1493 Fin15AnchoredAtom4034 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00632
  ] at hbad
  tauto

theorem fin15Anchored_clause25015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom4035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01144
  ] at hbad
  tauto

theorem fin15Anchored_clause25016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom4035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01144
  ] at hbad
  tauto

theorem fin15Anchored_clause25017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom4035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01144
  ] at hbad
  tauto

theorem fin15Anchored_clause25018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom4035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01144
  ] at hbad
  tauto

theorem fin15Anchored_clause25019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4035 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom4035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01144
  ] at hbad
  tauto

theorem fin15Anchored_clause25020 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4035 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom1330 Fin15AnchoredAtom1338
    Fin15AnchoredAtom1374 Fin15AnchoredAtom1494 Fin15AnchoredAtom4035 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01144
  ] at hbad
  tauto

theorem fin15Anchored_clause25021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4036 chi ∧
      ¬Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1495 Fin15AnchoredAtom4036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02168
  ] at hbad
  tauto

theorem fin15Anchored_clause25022 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4036 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1331 chi ∧
      Fin15AnchoredAtom1339 chi ∧
      Fin15AnchoredAtom1375 chi ∧
      Fin15AnchoredAtom1495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom1331 Fin15AnchoredAtom1339
    Fin15AnchoredAtom1375 Fin15AnchoredAtom1495 Fin15AnchoredAtom4036 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02168
  ] at hbad
  tauto

theorem fin15Anchored_clause25023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom4037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04216
  ] at hbad
  tauto

theorem fin15Anchored_clause25024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom4037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04216
  ] at hbad
  tauto

theorem fin15Anchored_clause25025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom4037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04216
  ] at hbad
  tauto

theorem fin15Anchored_clause25026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom4037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04216
  ] at hbad
  tauto

theorem fin15Anchored_clause25027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4037 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom4037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04216
  ] at hbad
  tauto

theorem fin15Anchored_clause25028 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4037 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom1332 Fin15AnchoredAtom1340
    Fin15AnchoredAtom1376 Fin15AnchoredAtom1496 Fin15AnchoredAtom4037 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04216
  ] at hbad
  tauto

theorem fin15Anchored_clause25029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom4038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08312
  ] at hbad
  tauto

theorem fin15Anchored_clause25030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom4038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08312
  ] at hbad
  tauto

theorem fin15Anchored_clause25031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom4038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08312
  ] at hbad
  tauto

theorem fin15Anchored_clause25032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom4038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08312
  ] at hbad
  tauto

theorem fin15Anchored_clause25033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4038 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom4038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08312
  ] at hbad
  tauto

theorem fin15Anchored_clause25034 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4038 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom1333 Fin15AnchoredAtom1341
    Fin15AnchoredAtom1377 Fin15AnchoredAtom1497 Fin15AnchoredAtom4038 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08312
  ] at hbad
  tauto

theorem fin15Anchored_clause25035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1326 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom4039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16504
  ] at hbad
  tauto

theorem fin15Anchored_clause25036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom4039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16504
  ] at hbad
  tauto

theorem fin15Anchored_clause25037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom4039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16504
  ] at hbad
  tauto

theorem fin15Anchored_clause25038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom4039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16504
  ] at hbad
  tauto

theorem fin15Anchored_clause25039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4039 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom4039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16504
  ] at hbad
  tauto

theorem fin15Anchored_clause25040 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4039 chi ∧
      Fin15AnchoredAtom1326 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1326 Fin15AnchoredAtom1334 Fin15AnchoredAtom1342
    Fin15AnchoredAtom1378 Fin15AnchoredAtom1498 Fin15AnchoredAtom4039 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16504
  ] at hbad
  tauto

theorem fin15Anchored_clause25041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom4040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00440
  ] at hbad
  tauto

theorem fin15Anchored_clause25042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom4040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00440
  ] at hbad
  tauto

theorem fin15Anchored_clause25043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom4040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00440
  ] at hbad
  tauto

theorem fin15Anchored_clause25044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4040 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom4040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00440
  ] at hbad
  tauto

theorem fin15Anchored_clause25045 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4040 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom1328 Fin15AnchoredAtom1343
    Fin15AnchoredAtom1379 Fin15AnchoredAtom1499 Fin15AnchoredAtom4040 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00440
  ] at hbad
  tauto

theorem fin15Anchored_clause25046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom4041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00696
  ] at hbad
  tauto

theorem fin15Anchored_clause25047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom4041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00696
  ] at hbad
  tauto

theorem fin15Anchored_clause25048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom4041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00696
  ] at hbad
  tauto

theorem fin15Anchored_clause25049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom4041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00696
  ] at hbad
  tauto

theorem fin15Anchored_clause25050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4041 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom4041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00696
  ] at hbad
  tauto

theorem fin15Anchored_clause25051 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4041 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom1329 Fin15AnchoredAtom1344
    Fin15AnchoredAtom1380 Fin15AnchoredAtom1500 Fin15AnchoredAtom4041 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00696
  ] at hbad
  tauto

theorem fin15Anchored_clause25052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom4042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01208
  ] at hbad
  tauto

theorem fin15Anchored_clause25053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom4042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01208
  ] at hbad
  tauto

theorem fin15Anchored_clause25054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom4042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01208
  ] at hbad
  tauto

theorem fin15Anchored_clause25055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom4042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01208
  ] at hbad
  tauto

theorem fin15Anchored_clause25056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4042 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom4042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01208
  ] at hbad
  tauto

theorem fin15Anchored_clause25057 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4042 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom1330 Fin15AnchoredAtom1345
    Fin15AnchoredAtom1381 Fin15AnchoredAtom1501 Fin15AnchoredAtom4042 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01208
  ] at hbad
  tauto

theorem fin15Anchored_clause25058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4043 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1502 Fin15AnchoredAtom4043 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02232
  ] at hbad
  tauto

theorem fin15Anchored_clause25059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom4044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04280
  ] at hbad
  tauto

theorem fin15Anchored_clause25060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom4044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04280
  ] at hbad
  tauto

theorem fin15Anchored_clause25061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom4044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04280
  ] at hbad
  tauto

theorem fin15Anchored_clause25062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom4044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04280
  ] at hbad
  tauto

theorem fin15Anchored_clause25063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4044 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom4044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04280
  ] at hbad
  tauto

theorem fin15Anchored_clause25064 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4044 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom1332 Fin15AnchoredAtom1347
    Fin15AnchoredAtom1383 Fin15AnchoredAtom1503 Fin15AnchoredAtom4044 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04280
  ] at hbad
  tauto

theorem fin15Anchored_clause25065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom4045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08376
  ] at hbad
  tauto

theorem fin15Anchored_clause25066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom4045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08376
  ] at hbad
  tauto

theorem fin15Anchored_clause25067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom4045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08376
  ] at hbad
  tauto

theorem fin15Anchored_clause25068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom4045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08376
  ] at hbad
  tauto

theorem fin15Anchored_clause25069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4045 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom4045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08376
  ] at hbad
  tauto

theorem fin15Anchored_clause25070 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4045 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom1333 Fin15AnchoredAtom1348
    Fin15AnchoredAtom1384 Fin15AnchoredAtom1504 Fin15AnchoredAtom4045 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08376
  ] at hbad
  tauto

theorem fin15Anchored_clause25071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1327 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom4046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16568
  ] at hbad
  tauto

theorem fin15Anchored_clause25072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom4046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16568
  ] at hbad
  tauto

theorem fin15Anchored_clause25073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom4046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16568
  ] at hbad
  tauto

theorem fin15Anchored_clause25074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom4046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16568
  ] at hbad
  tauto

theorem fin15Anchored_clause25075 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4046 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom4046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16568
  ] at hbad
  tauto

theorem fin15Anchored_clause25076 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4046 chi ∧
      Fin15AnchoredAtom1327 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1327 Fin15AnchoredAtom1334 Fin15AnchoredAtom1349
    Fin15AnchoredAtom1385 Fin15AnchoredAtom1505 Fin15AnchoredAtom4046 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16568
  ] at hbad
  tauto

theorem fin15Anchored_clause25077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom4047 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00824
  ] at hbad
  tauto

theorem fin15Anchored_clause25078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom4047 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00824
  ] at hbad
  tauto

theorem fin15Anchored_clause25079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom1350 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1350 Fin15AnchoredAtom4047 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00824
  ] at hbad
  tauto

theorem fin15Anchored_clause25080 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4047 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom4047 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00824
  ] at hbad
  tauto

theorem fin15Anchored_clause25081 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4047 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1350 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom1329 Fin15AnchoredAtom1350
    Fin15AnchoredAtom1386 Fin15AnchoredAtom1506 Fin15AnchoredAtom4047 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00824
  ] at hbad
  tauto

theorem fin15Anchored_clause25082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom4048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01336
  ] at hbad
  tauto

theorem fin15Anchored_clause25083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom4048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01336
  ] at hbad
  tauto

theorem fin15Anchored_clause25084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1351 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1351 Fin15AnchoredAtom4048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01336
  ] at hbad
  tauto

theorem fin15Anchored_clause25085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom4048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01336
  ] at hbad
  tauto

theorem fin15Anchored_clause25086 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4048 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom4048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01336
  ] at hbad
  tauto

theorem fin15Anchored_clause25087 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4048 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1351 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom1330 Fin15AnchoredAtom1351
    Fin15AnchoredAtom1387 Fin15AnchoredAtom1507 Fin15AnchoredAtom4048 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01336
  ] at hbad
  tauto

end ErdosSzekeres

end
