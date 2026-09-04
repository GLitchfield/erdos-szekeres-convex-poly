module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 196. -/

theorem fin15Anchored_clause25088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom4050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04408
  ] at hbad
  tauto

theorem fin15Anchored_clause25089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom4050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04408
  ] at hbad
  tauto

theorem fin15Anchored_clause25090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1353 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1353 Fin15AnchoredAtom4050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04408
  ] at hbad
  tauto

theorem fin15Anchored_clause25091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1389 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1389 Fin15AnchoredAtom4050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04408
  ] at hbad
  tauto

theorem fin15Anchored_clause25092 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4050 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom4050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04408
  ] at hbad
  tauto

theorem fin15Anchored_clause25093 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4050 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1353 chi ∧
      Fin15AnchoredAtom1389 chi ∧
      Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom1332 Fin15AnchoredAtom1353
    Fin15AnchoredAtom1389 Fin15AnchoredAtom1509 Fin15AnchoredAtom4050 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04408
  ] at hbad
  tauto

theorem fin15Anchored_clause25094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom4051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08504
  ] at hbad
  tauto

theorem fin15Anchored_clause25095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom4051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08504
  ] at hbad
  tauto

theorem fin15Anchored_clause25096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1354 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1354 Fin15AnchoredAtom4051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08504
  ] at hbad
  tauto

theorem fin15Anchored_clause25097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1390 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1390 Fin15AnchoredAtom4051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08504
  ] at hbad
  tauto

theorem fin15Anchored_clause25098 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4051 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom4051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08504
  ] at hbad
  tauto

theorem fin15Anchored_clause25099 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4051 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1354 chi ∧
      Fin15AnchoredAtom1390 chi ∧
      Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom1333 Fin15AnchoredAtom1354
    Fin15AnchoredAtom1390 Fin15AnchoredAtom1510 Fin15AnchoredAtom4051 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08504
  ] at hbad
  tauto

theorem fin15Anchored_clause25100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1328 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom4052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16696
  ] at hbad
  tauto

theorem fin15Anchored_clause25101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom4052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16696
  ] at hbad
  tauto

theorem fin15Anchored_clause25102 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1355 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1355 Fin15AnchoredAtom4052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16696
  ] at hbad
  tauto

theorem fin15Anchored_clause25103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1391 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1391 Fin15AnchoredAtom4052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16696
  ] at hbad
  tauto

theorem fin15Anchored_clause25104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4052 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1511 Fin15AnchoredAtom4052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16696
  ] at hbad
  tauto

theorem fin15Anchored_clause25105 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4052 chi ∧
      Fin15AnchoredAtom1328 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1355 chi ∧
      Fin15AnchoredAtom1391 chi ∧
      Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1328 Fin15AnchoredAtom1334 Fin15AnchoredAtom1355
    Fin15AnchoredAtom1391 Fin15AnchoredAtom1511 Fin15AnchoredAtom4052 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16696
  ] at hbad
  tauto

theorem fin15Anchored_clause25106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom4053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01592
  ] at hbad
  tauto

theorem fin15Anchored_clause25107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom4053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01592
  ] at hbad
  tauto

theorem fin15Anchored_clause25108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom4053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01592
  ] at hbad
  tauto

theorem fin15Anchored_clause25109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1392 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1392 Fin15AnchoredAtom4053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01592
  ] at hbad
  tauto

theorem fin15Anchored_clause25110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4053 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom4053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01592
  ] at hbad
  tauto

theorem fin15Anchored_clause25111 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4053 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1392 chi ∧
      Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom1330 Fin15AnchoredAtom1356
    Fin15AnchoredAtom1392 Fin15AnchoredAtom1512 Fin15AnchoredAtom4053 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01592
  ] at hbad
  tauto

theorem fin15Anchored_clause25112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4054 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom4054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02616
  ] at hbad
  tauto

theorem fin15Anchored_clause25113 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4054 chi ∧
      ¬Fin15AnchoredAtom1357 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1357 Fin15AnchoredAtom4054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02616
  ] at hbad
  tauto

theorem fin15Anchored_clause25114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4054 chi ∧
      ¬Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1513 Fin15AnchoredAtom4054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02616
  ] at hbad
  tauto

theorem fin15Anchored_clause25115 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4054 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1331 chi ∧
      Fin15AnchoredAtom1357 chi ∧
      Fin15AnchoredAtom1393 chi ∧
      Fin15AnchoredAtom1513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom1331 Fin15AnchoredAtom1357
    Fin15AnchoredAtom1393 Fin15AnchoredAtom1513 Fin15AnchoredAtom4054 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02616
  ] at hbad
  tauto

theorem fin15Anchored_clause25116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom4055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04664
  ] at hbad
  tauto

theorem fin15Anchored_clause25117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom4055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04664
  ] at hbad
  tauto

theorem fin15Anchored_clause25118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom4055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04664
  ] at hbad
  tauto

theorem fin15Anchored_clause25119 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1394 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1394 Fin15AnchoredAtom4055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04664
  ] at hbad
  tauto

theorem fin15Anchored_clause25120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4055 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom4055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04664
  ] at hbad
  tauto

theorem fin15Anchored_clause25121 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4055 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1394 chi ∧
      Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom1332 Fin15AnchoredAtom1358
    Fin15AnchoredAtom1394 Fin15AnchoredAtom1514 Fin15AnchoredAtom4055 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04664
  ] at hbad
  tauto

theorem fin15Anchored_clause25122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom4056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08760
  ] at hbad
  tauto

theorem fin15Anchored_clause25123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom4056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08760
  ] at hbad
  tauto

theorem fin15Anchored_clause25124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom4056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08760
  ] at hbad
  tauto

theorem fin15Anchored_clause25125 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1395 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1395 Fin15AnchoredAtom4056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08760
  ] at hbad
  tauto

theorem fin15Anchored_clause25126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4056 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom4056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08760
  ] at hbad
  tauto

theorem fin15Anchored_clause25127 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4056 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1395 chi ∧
      Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom1333 Fin15AnchoredAtom1359
    Fin15AnchoredAtom1395 Fin15AnchoredAtom1515 Fin15AnchoredAtom4056 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08760
  ] at hbad
  tauto

theorem fin15Anchored_clause25128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1329 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom4057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16952
  ] at hbad
  tauto

theorem fin15Anchored_clause25129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom4057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16952
  ] at hbad
  tauto

theorem fin15Anchored_clause25130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom4057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16952
  ] at hbad
  tauto

theorem fin15Anchored_clause25131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1396 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1396 Fin15AnchoredAtom4057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16952
  ] at hbad
  tauto

theorem fin15Anchored_clause25132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4057 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom4057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16952
  ] at hbad
  tauto

theorem fin15Anchored_clause25133 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4057 chi ∧
      Fin15AnchoredAtom1329 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1396 chi ∧
      Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1329 Fin15AnchoredAtom1334 Fin15AnchoredAtom1360
    Fin15AnchoredAtom1396 Fin15AnchoredAtom1516 Fin15AnchoredAtom4057 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16952
  ] at hbad
  tauto

theorem fin15Anchored_clause25134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4058 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom4058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03128
  ] at hbad
  tauto

theorem fin15Anchored_clause25135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4058 chi ∧
      ¬Fin15AnchoredAtom1397 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1397 Fin15AnchoredAtom4058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03128
  ] at hbad
  tauto

theorem fin15Anchored_clause25136 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4058 chi ∧
      ¬Fin15AnchoredAtom1517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1517 Fin15AnchoredAtom4058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03128
  ] at hbad
  tauto

theorem fin15Anchored_clause25137 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4058 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1331 chi ∧
      Fin15AnchoredAtom1361 chi ∧
      Fin15AnchoredAtom1397 chi ∧
      Fin15AnchoredAtom1517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom1331 Fin15AnchoredAtom1361
    Fin15AnchoredAtom1397 Fin15AnchoredAtom1517 Fin15AnchoredAtom4058 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03128
  ] at hbad
  tauto

theorem fin15Anchored_clause25138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom4059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05176
  ] at hbad
  tauto

theorem fin15Anchored_clause25139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom4059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05176
  ] at hbad
  tauto

theorem fin15Anchored_clause25140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom4059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05176
  ] at hbad
  tauto

theorem fin15Anchored_clause25141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1398 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1398 Fin15AnchoredAtom4059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05176
  ] at hbad
  tauto

theorem fin15Anchored_clause25142 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4059 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom4059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05176
  ] at hbad
  tauto

theorem fin15Anchored_clause25143 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4059 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1398 chi ∧
      Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom1332 Fin15AnchoredAtom1362
    Fin15AnchoredAtom1398 Fin15AnchoredAtom1518 Fin15AnchoredAtom4059 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05176
  ] at hbad
  tauto

theorem fin15Anchored_clause25144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom4060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09272
  ] at hbad
  tauto

theorem fin15Anchored_clause25145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom4060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09272
  ] at hbad
  tauto

theorem fin15Anchored_clause25146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom4060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09272
  ] at hbad
  tauto

theorem fin15Anchored_clause25147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1399 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1399 Fin15AnchoredAtom4060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09272
  ] at hbad
  tauto

theorem fin15Anchored_clause25148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4060 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom4060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09272
  ] at hbad
  tauto

theorem fin15Anchored_clause25149 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4060 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1399 chi ∧
      Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom1333 Fin15AnchoredAtom1363
    Fin15AnchoredAtom1399 Fin15AnchoredAtom1519 Fin15AnchoredAtom4060 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09272
  ] at hbad
  tauto

theorem fin15Anchored_clause25150 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1330 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom4061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17464
  ] at hbad
  tauto

theorem fin15Anchored_clause25151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom4061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17464
  ] at hbad
  tauto

theorem fin15Anchored_clause25152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom4061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17464
  ] at hbad
  tauto

theorem fin15Anchored_clause25153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1400 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1400 Fin15AnchoredAtom4061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17464
  ] at hbad
  tauto

theorem fin15Anchored_clause25154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4061 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom4061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17464
  ] at hbad
  tauto

theorem fin15Anchored_clause25155 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4061 chi ∧
      Fin15AnchoredAtom1330 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1400 chi ∧
      Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1330 Fin15AnchoredAtom1334 Fin15AnchoredAtom1364
    Fin15AnchoredAtom1400 Fin15AnchoredAtom1520 Fin15AnchoredAtom4061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17464
  ] at hbad
  tauto

theorem fin15Anchored_clause25156 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4062 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom4062 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06200
  ] at hbad
  tauto

theorem fin15Anchored_clause25157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4063 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom4063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10296
  ] at hbad
  tauto

theorem fin15Anchored_clause25158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4064 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom4064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18488
  ] at hbad
  tauto

theorem fin15Anchored_clause25159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4064 chi ∧
      ¬Fin15AnchoredAtom1367 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1367 Fin15AnchoredAtom4064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18488
  ] at hbad
  tauto

theorem fin15Anchored_clause25160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom4065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12344
  ] at hbad
  tauto

theorem fin15Anchored_clause25161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom4065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12344
  ] at hbad
  tauto

theorem fin15Anchored_clause25162 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom4065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12344
  ] at hbad
  tauto

theorem fin15Anchored_clause25163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1404 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1404 Fin15AnchoredAtom4065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12344
  ] at hbad
  tauto

theorem fin15Anchored_clause25164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4065 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom4065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12344
  ] at hbad
  tauto

theorem fin15Anchored_clause25165 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4065 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1404 chi ∧
      Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom1333 Fin15AnchoredAtom1368
    Fin15AnchoredAtom1404 Fin15AnchoredAtom1524 Fin15AnchoredAtom4065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12344
  ] at hbad
  tauto

theorem fin15Anchored_clause25166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1332 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom4066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20536
  ] at hbad
  tauto

theorem fin15Anchored_clause25167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom4066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20536
  ] at hbad
  tauto

theorem fin15Anchored_clause25168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom4066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20536
  ] at hbad
  tauto

theorem fin15Anchored_clause25169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1405 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1405 Fin15AnchoredAtom4066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20536
  ] at hbad
  tauto

theorem fin15Anchored_clause25170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4066 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom4066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20536
  ] at hbad
  tauto

theorem fin15Anchored_clause25171 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4066 chi ∧
      Fin15AnchoredAtom1332 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1405 chi ∧
      Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1332 Fin15AnchoredAtom1334 Fin15AnchoredAtom1369
    Fin15AnchoredAtom1405 Fin15AnchoredAtom1525 Fin15AnchoredAtom4066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20536
  ] at hbad
  tauto

theorem fin15Anchored_clause25172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1333 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom4067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24632
  ] at hbad
  tauto

theorem fin15Anchored_clause25173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1334 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1334 Fin15AnchoredAtom4067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24632
  ] at hbad
  tauto

theorem fin15Anchored_clause25174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom4067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24632
  ] at hbad
  tauto

theorem fin15Anchored_clause25175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1406 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1406 Fin15AnchoredAtom4067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24632
  ] at hbad
  tauto

theorem fin15Anchored_clause25176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4067 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom4067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24632
  ] at hbad
  tauto

theorem fin15Anchored_clause25177 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4067 chi ∧
      Fin15AnchoredAtom1333 chi ∧
      Fin15AnchoredAtom1334 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1406 chi ∧
      Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1333 Fin15AnchoredAtom1334 Fin15AnchoredAtom1370
    Fin15AnchoredAtom1406 Fin15AnchoredAtom1526 Fin15AnchoredAtom4067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24632
  ] at hbad
  tauto

theorem fin15Anchored_clause25178 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom4068 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00472
  ] at hbad
  tauto

theorem fin15Anchored_clause25179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom4068 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00472
  ] at hbad
  tauto

theorem fin15Anchored_clause25180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1343 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1343 Fin15AnchoredAtom4068 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00472
  ] at hbad
  tauto

theorem fin15Anchored_clause25181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom4068 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00472
  ] at hbad
  tauto

theorem fin15Anchored_clause25182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4068 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom4068 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00472
  ] at hbad
  tauto

theorem fin15Anchored_clause25183 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4068 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1336 chi ∧
      Fin15AnchoredAtom1343 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom1336 Fin15AnchoredAtom1343
    Fin15AnchoredAtom1407 Fin15AnchoredAtom1527 Fin15AnchoredAtom4068 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00472
  ] at hbad
  tauto

theorem fin15Anchored_clause25184 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom4069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00728
  ] at hbad
  tauto

theorem fin15Anchored_clause25185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1337 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1337 Fin15AnchoredAtom4069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00728
  ] at hbad
  tauto

theorem fin15Anchored_clause25186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1344 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1344 Fin15AnchoredAtom4069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00728
  ] at hbad
  tauto

theorem fin15Anchored_clause25187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom4069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00728
  ] at hbad
  tauto

theorem fin15Anchored_clause25188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4069 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom4069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00728
  ] at hbad
  tauto

theorem fin15Anchored_clause25189 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4069 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1337 chi ∧
      Fin15AnchoredAtom1344 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom1337 Fin15AnchoredAtom1344
    Fin15AnchoredAtom1408 Fin15AnchoredAtom1528 Fin15AnchoredAtom4069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00728
  ] at hbad
  tauto

theorem fin15Anchored_clause25190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom4070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01240
  ] at hbad
  tauto

theorem fin15Anchored_clause25191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1338 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1338 Fin15AnchoredAtom4070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01240
  ] at hbad
  tauto

theorem fin15Anchored_clause25192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1345 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1345 Fin15AnchoredAtom4070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01240
  ] at hbad
  tauto

theorem fin15Anchored_clause25193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom4070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01240
  ] at hbad
  tauto

theorem fin15Anchored_clause25194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4070 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom4070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01240
  ] at hbad
  tauto

theorem fin15Anchored_clause25195 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4070 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1338 chi ∧
      Fin15AnchoredAtom1345 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom1338 Fin15AnchoredAtom1345
    Fin15AnchoredAtom1409 Fin15AnchoredAtom1529 Fin15AnchoredAtom4070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01240
  ] at hbad
  tauto

theorem fin15Anchored_clause25196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4071 chi ∧
      ¬Fin15AnchoredAtom1530 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1530 Fin15AnchoredAtom4071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02264
  ] at hbad
  tauto

theorem fin15Anchored_clause25197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom4072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04312
  ] at hbad
  tauto

theorem fin15Anchored_clause25198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1340 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1340 Fin15AnchoredAtom4072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04312
  ] at hbad
  tauto

theorem fin15Anchored_clause25199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1347 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1347 Fin15AnchoredAtom4072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04312
  ] at hbad
  tauto

theorem fin15Anchored_clause25200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom4072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04312
  ] at hbad
  tauto

theorem fin15Anchored_clause25201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4072 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom4072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04312
  ] at hbad
  tauto

theorem fin15Anchored_clause25202 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4072 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1340 chi ∧
      Fin15AnchoredAtom1347 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom1340 Fin15AnchoredAtom1347
    Fin15AnchoredAtom1411 Fin15AnchoredAtom1531 Fin15AnchoredAtom4072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04312
  ] at hbad
  tauto

theorem fin15Anchored_clause25203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom4073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08408
  ] at hbad
  tauto

theorem fin15Anchored_clause25204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1341 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1341 Fin15AnchoredAtom4073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08408
  ] at hbad
  tauto

theorem fin15Anchored_clause25205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1348 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1348 Fin15AnchoredAtom4073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08408
  ] at hbad
  tauto

theorem fin15Anchored_clause25206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom4073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08408
  ] at hbad
  tauto

theorem fin15Anchored_clause25207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4073 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom4073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08408
  ] at hbad
  tauto

theorem fin15Anchored_clause25208 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4073 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1341 chi ∧
      Fin15AnchoredAtom1348 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom1341 Fin15AnchoredAtom1348
    Fin15AnchoredAtom1412 Fin15AnchoredAtom1532 Fin15AnchoredAtom4073 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08408
  ] at hbad
  tauto

theorem fin15Anchored_clause25209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1335 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom4074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16600
  ] at hbad
  tauto

theorem fin15Anchored_clause25210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1342 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1342 Fin15AnchoredAtom4074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16600
  ] at hbad
  tauto

theorem fin15Anchored_clause25211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1349 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1349 Fin15AnchoredAtom4074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16600
  ] at hbad
  tauto

theorem fin15Anchored_clause25212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom4074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16600
  ] at hbad
  tauto

theorem fin15Anchored_clause25213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4074 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom4074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16600
  ] at hbad
  tauto

theorem fin15Anchored_clause25214 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4074 chi ∧
      Fin15AnchoredAtom1335 chi ∧
      Fin15AnchoredAtom1342 chi ∧
      Fin15AnchoredAtom1349 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1335 Fin15AnchoredAtom1342 Fin15AnchoredAtom1349
    Fin15AnchoredAtom1413 Fin15AnchoredAtom1533 Fin15AnchoredAtom4074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16600
  ] at hbad
  tauto

theorem fin15Anchored_clause25215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4075 chi ∧
      ¬Fin15AnchoredAtom1336 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1336 Fin15AnchoredAtom4075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00856
  ] at hbad
  tauto

end ErdosSzekeres

end
