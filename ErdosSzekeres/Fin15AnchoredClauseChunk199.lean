module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 199. -/

theorem fin15Anchored_clause25472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom4133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05656
  ] at hbad
  tauto

theorem fin15Anchored_clause25473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom4133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05656
  ] at hbad
  tauto

theorem fin15Anchored_clause25474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom4133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05656
  ] at hbad
  tauto

theorem fin15Anchored_clause25475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1472 Fin15AnchoredAtom4133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05656
  ] at hbad
  tauto

theorem fin15Anchored_clause25476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4133 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom4133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05656
  ] at hbad
  tauto

theorem fin15Anchored_clause25477 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4133 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1472 chi ∧
      Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom1358 Fin15AnchoredAtom1362
    Fin15AnchoredAtom1472 Fin15AnchoredAtom1592 Fin15AnchoredAtom4133 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05656
  ] at hbad
  tauto

theorem fin15Anchored_clause25478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom4134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09752
  ] at hbad
  tauto

theorem fin15Anchored_clause25479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom4134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09752
  ] at hbad
  tauto

theorem fin15Anchored_clause25480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom4134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09752
  ] at hbad
  tauto

theorem fin15Anchored_clause25481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1473 Fin15AnchoredAtom4134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09752
  ] at hbad
  tauto

theorem fin15Anchored_clause25482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4134 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom4134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09752
  ] at hbad
  tauto

theorem fin15Anchored_clause25483 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4134 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1473 chi ∧
      Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom1359 Fin15AnchoredAtom1363
    Fin15AnchoredAtom1473 Fin15AnchoredAtom1593 Fin15AnchoredAtom4134 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09752
  ] at hbad
  tauto

theorem fin15Anchored_clause25484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1356 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom4135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17944
  ] at hbad
  tauto

theorem fin15Anchored_clause25485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom4135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17944
  ] at hbad
  tauto

theorem fin15Anchored_clause25486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom4135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17944
  ] at hbad
  tauto

theorem fin15Anchored_clause25487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1474 Fin15AnchoredAtom4135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17944
  ] at hbad
  tauto

theorem fin15Anchored_clause25488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4135 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom4135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17944
  ] at hbad
  tauto

theorem fin15Anchored_clause25489 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4135 chi ∧
      Fin15AnchoredAtom1356 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1474 chi ∧
      Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1356 Fin15AnchoredAtom1360 Fin15AnchoredAtom1364
    Fin15AnchoredAtom1474 Fin15AnchoredAtom1594 Fin15AnchoredAtom4135 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17944
  ] at hbad
  tauto

theorem fin15Anchored_clause25490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4136 chi ∧
      ¬Fin15AnchoredAtom1475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1475 Fin15AnchoredAtom4136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06680
  ] at hbad
  tauto

theorem fin15Anchored_clause25491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4136 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1595 Fin15AnchoredAtom4136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06680
  ] at hbad
  tauto

theorem fin15Anchored_clause25492 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4136 chi ∧
      Fin15AnchoredAtom1357 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1365 chi ∧
      Fin15AnchoredAtom1475 chi ∧
      Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1357 Fin15AnchoredAtom1358 Fin15AnchoredAtom1365
    Fin15AnchoredAtom1475 Fin15AnchoredAtom1595 Fin15AnchoredAtom4136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06680
  ] at hbad
  tauto

theorem fin15Anchored_clause25493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4137 chi ∧
      ¬Fin15AnchoredAtom1476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1476 Fin15AnchoredAtom4137 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10776
  ] at hbad
  tauto

theorem fin15Anchored_clause25494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4137 chi ∧
      ¬Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1596 Fin15AnchoredAtom4137 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10776
  ] at hbad
  tauto

theorem fin15Anchored_clause25495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4138 chi ∧
      ¬Fin15AnchoredAtom1367 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1367 Fin15AnchoredAtom4138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18968
  ] at hbad
  tauto

theorem fin15Anchored_clause25496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4138 chi ∧
      ¬Fin15AnchoredAtom1597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1597 Fin15AnchoredAtom4138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18968
  ] at hbad
  tauto

theorem fin15Anchored_clause25497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom4139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12824
  ] at hbad
  tauto

theorem fin15Anchored_clause25498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom4139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12824
  ] at hbad
  tauto

theorem fin15Anchored_clause25499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom4139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12824
  ] at hbad
  tauto

theorem fin15Anchored_clause25500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1478 Fin15AnchoredAtom4139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12824
  ] at hbad
  tauto

theorem fin15Anchored_clause25501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4139 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom4139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12824
  ] at hbad
  tauto

theorem fin15Anchored_clause25502 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4139 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1478 chi ∧
      Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom1359 Fin15AnchoredAtom1368
    Fin15AnchoredAtom1478 Fin15AnchoredAtom1598 Fin15AnchoredAtom4139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12824
  ] at hbad
  tauto

theorem fin15Anchored_clause25503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1358 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom4140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21016
  ] at hbad
  tauto

theorem fin15Anchored_clause25504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom4140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21016
  ] at hbad
  tauto

theorem fin15Anchored_clause25505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom4140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21016
  ] at hbad
  tauto

theorem fin15Anchored_clause25506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1479 Fin15AnchoredAtom4140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21016
  ] at hbad
  tauto

theorem fin15Anchored_clause25507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4140 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom4140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21016
  ] at hbad
  tauto

theorem fin15Anchored_clause25508 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4140 chi ∧
      Fin15AnchoredAtom1358 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1479 chi ∧
      Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1358 Fin15AnchoredAtom1360 Fin15AnchoredAtom1369
    Fin15AnchoredAtom1479 Fin15AnchoredAtom1599 Fin15AnchoredAtom4140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21016
  ] at hbad
  tauto

theorem fin15Anchored_clause25509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1359 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom4141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25112
  ] at hbad
  tauto

theorem fin15Anchored_clause25510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1360 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1360 Fin15AnchoredAtom4141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25112
  ] at hbad
  tauto

theorem fin15Anchored_clause25511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom4141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25112
  ] at hbad
  tauto

theorem fin15Anchored_clause25512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1480 Fin15AnchoredAtom4141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25112
  ] at hbad
  tauto

theorem fin15Anchored_clause25513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4141 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom4141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25112
  ] at hbad
  tauto

theorem fin15Anchored_clause25514 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4141 chi ∧
      Fin15AnchoredAtom1359 chi ∧
      Fin15AnchoredAtom1360 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1480 chi ∧
      Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1359 Fin15AnchoredAtom1360 Fin15AnchoredAtom1370
    Fin15AnchoredAtom1480 Fin15AnchoredAtom1600 Fin15AnchoredAtom4141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25112
  ] at hbad
  tauto

theorem fin15Anchored_clause25515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4142 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom4142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07192
  ] at hbad
  tauto

theorem fin15Anchored_clause25516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4142 chi ∧
      ¬Fin15AnchoredAtom1365 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1365 Fin15AnchoredAtom4142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07192
  ] at hbad
  tauto

theorem fin15Anchored_clause25517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4142 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1601 Fin15AnchoredAtom4142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07192
  ] at hbad
  tauto

theorem fin15Anchored_clause25518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4143 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom4143 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11288
  ] at hbad
  tauto

theorem fin15Anchored_clause25519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4143 chi ∧
      ¬Fin15AnchoredAtom1482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1482 Fin15AnchoredAtom4143 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11288
  ] at hbad
  tauto

theorem fin15Anchored_clause25520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4143 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1602 Fin15AnchoredAtom4143 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11288
  ] at hbad
  tauto

theorem fin15Anchored_clause25521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom4145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13336
  ] at hbad
  tauto

theorem fin15Anchored_clause25522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom4145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13336
  ] at hbad
  tauto

theorem fin15Anchored_clause25523 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom4145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13336
  ] at hbad
  tauto

theorem fin15Anchored_clause25524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom4145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13336
  ] at hbad
  tauto

theorem fin15Anchored_clause25525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4145 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom4145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13336
  ] at hbad
  tauto

theorem fin15Anchored_clause25526 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4145 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom1363 Fin15AnchoredAtom1368
    Fin15AnchoredAtom1484 Fin15AnchoredAtom1604 Fin15AnchoredAtom4145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13336
  ] at hbad
  tauto

theorem fin15Anchored_clause25527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1362 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom4146 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21528
  ] at hbad
  tauto

theorem fin15Anchored_clause25528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom4146 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21528
  ] at hbad
  tauto

theorem fin15Anchored_clause25529 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom4146 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21528
  ] at hbad
  tauto

theorem fin15Anchored_clause25530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom4146 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21528
  ] at hbad
  tauto

theorem fin15Anchored_clause25531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4146 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom4146 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21528
  ] at hbad
  tauto

theorem fin15Anchored_clause25532 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4146 chi ∧
      Fin15AnchoredAtom1362 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1362 Fin15AnchoredAtom1364 Fin15AnchoredAtom1369
    Fin15AnchoredAtom1485 Fin15AnchoredAtom1605 Fin15AnchoredAtom4146 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21528
  ] at hbad
  tauto

theorem fin15Anchored_clause25533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1363 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom4147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25624
  ] at hbad
  tauto

theorem fin15Anchored_clause25534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1364 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1364 Fin15AnchoredAtom4147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25624
  ] at hbad
  tauto

theorem fin15Anchored_clause25535 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom4147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25624
  ] at hbad
  tauto

theorem fin15Anchored_clause25536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom4147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25624
  ] at hbad
  tauto

theorem fin15Anchored_clause25537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4147 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom4147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25624
  ] at hbad
  tauto

theorem fin15Anchored_clause25538 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4147 chi ∧
      Fin15AnchoredAtom1363 chi ∧
      Fin15AnchoredAtom1364 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1363 Fin15AnchoredAtom1364 Fin15AnchoredAtom1370
    Fin15AnchoredAtom1486 Fin15AnchoredAtom1606 Fin15AnchoredAtom4147 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25624
  ] at hbad
  tauto

theorem fin15Anchored_clause25539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4148 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1607 Fin15AnchoredAtom4148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14360
  ] at hbad
  tauto

theorem fin15Anchored_clause25540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4149 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom4149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22552
  ] at hbad
  tauto

theorem fin15Anchored_clause25541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1368 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom4151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28696
  ] at hbad
  tauto

theorem fin15Anchored_clause25542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1369 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1369 Fin15AnchoredAtom4151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28696
  ] at hbad
  tauto

theorem fin15Anchored_clause25543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1370 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1370 Fin15AnchoredAtom4151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28696
  ] at hbad
  tauto

theorem fin15Anchored_clause25544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom4151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28696
  ] at hbad
  tauto

theorem fin15Anchored_clause25545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4151 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom4151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28696
  ] at hbad
  tauto

theorem fin15Anchored_clause25546 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4151 chi ∧
      Fin15AnchoredAtom1368 chi ∧
      Fin15AnchoredAtom1369 chi ∧
      Fin15AnchoredAtom1370 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1368 Fin15AnchoredAtom1369 Fin15AnchoredAtom1370
    Fin15AnchoredAtom1490 Fin15AnchoredAtom1610 Fin15AnchoredAtom4151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28696
  ] at hbad
  tauto

theorem fin15Anchored_clause25547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom4152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00488
  ] at hbad
  tauto

theorem fin15Anchored_clause25548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom4152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00488
  ] at hbad
  tauto

theorem fin15Anchored_clause25549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1379 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1379 Fin15AnchoredAtom4152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00488
  ] at hbad
  tauto

theorem fin15Anchored_clause25550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1407 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1407 Fin15AnchoredAtom4152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00488
  ] at hbad
  tauto

theorem fin15Anchored_clause25551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4152 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom4152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00488
  ] at hbad
  tauto

theorem fin15Anchored_clause25552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4152 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1379 chi ∧
      Fin15AnchoredAtom1407 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom1372 Fin15AnchoredAtom1379
    Fin15AnchoredAtom1407 Fin15AnchoredAtom1611 Fin15AnchoredAtom4152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00488
  ] at hbad
  tauto

theorem fin15Anchored_clause25553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom4153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00744
  ] at hbad
  tauto

theorem fin15Anchored_clause25554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom4153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00744
  ] at hbad
  tauto

theorem fin15Anchored_clause25555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1380 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1380 Fin15AnchoredAtom4153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00744
  ] at hbad
  tauto

theorem fin15Anchored_clause25556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1408 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1408 Fin15AnchoredAtom4153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00744
  ] at hbad
  tauto

theorem fin15Anchored_clause25557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4153 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom4153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00744
  ] at hbad
  tauto

theorem fin15Anchored_clause25558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4153 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1380 chi ∧
      Fin15AnchoredAtom1408 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom1373 Fin15AnchoredAtom1380
    Fin15AnchoredAtom1408 Fin15AnchoredAtom1612 Fin15AnchoredAtom4153 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00744
  ] at hbad
  tauto

theorem fin15Anchored_clause25559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom4154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01256
  ] at hbad
  tauto

theorem fin15Anchored_clause25560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom4154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01256
  ] at hbad
  tauto

theorem fin15Anchored_clause25561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1381 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1381 Fin15AnchoredAtom4154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01256
  ] at hbad
  tauto

theorem fin15Anchored_clause25562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1409 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1409 Fin15AnchoredAtom4154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01256
  ] at hbad
  tauto

theorem fin15Anchored_clause25563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4154 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom4154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01256
  ] at hbad
  tauto

theorem fin15Anchored_clause25564 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4154 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1381 chi ∧
      Fin15AnchoredAtom1409 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom1374 Fin15AnchoredAtom1381
    Fin15AnchoredAtom1409 Fin15AnchoredAtom1613 Fin15AnchoredAtom4154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01256
  ] at hbad
  tauto

theorem fin15Anchored_clause25565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4155 chi ∧
      ¬Fin15AnchoredAtom1410 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1410 Fin15AnchoredAtom4155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02280
  ] at hbad
  tauto

theorem fin15Anchored_clause25566 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4155 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1375 chi ∧
      Fin15AnchoredAtom1382 chi ∧
      Fin15AnchoredAtom1410 chi ∧
      Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom1375 Fin15AnchoredAtom1382
    Fin15AnchoredAtom1410 Fin15AnchoredAtom1614 Fin15AnchoredAtom4155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02280
  ] at hbad
  tauto

theorem fin15Anchored_clause25567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom4156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04328
  ] at hbad
  tauto

theorem fin15Anchored_clause25568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom4156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04328
  ] at hbad
  tauto

theorem fin15Anchored_clause25569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1383 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1383 Fin15AnchoredAtom4156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04328
  ] at hbad
  tauto

theorem fin15Anchored_clause25570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1411 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1411 Fin15AnchoredAtom4156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04328
  ] at hbad
  tauto

theorem fin15Anchored_clause25571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4156 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom4156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04328
  ] at hbad
  tauto

theorem fin15Anchored_clause25572 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4156 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1376 chi ∧
      Fin15AnchoredAtom1383 chi ∧
      Fin15AnchoredAtom1411 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom1376 Fin15AnchoredAtom1383
    Fin15AnchoredAtom1411 Fin15AnchoredAtom1615 Fin15AnchoredAtom4156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04328
  ] at hbad
  tauto

theorem fin15Anchored_clause25573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom4157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08424
  ] at hbad
  tauto

theorem fin15Anchored_clause25574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1377 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1377 Fin15AnchoredAtom4157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08424
  ] at hbad
  tauto

theorem fin15Anchored_clause25575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1384 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1384 Fin15AnchoredAtom4157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08424
  ] at hbad
  tauto

theorem fin15Anchored_clause25576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1412 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1412 Fin15AnchoredAtom4157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08424
  ] at hbad
  tauto

theorem fin15Anchored_clause25577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4157 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom4157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08424
  ] at hbad
  tauto

theorem fin15Anchored_clause25578 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4157 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1377 chi ∧
      Fin15AnchoredAtom1384 chi ∧
      Fin15AnchoredAtom1412 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom1377 Fin15AnchoredAtom1384
    Fin15AnchoredAtom1412 Fin15AnchoredAtom1616 Fin15AnchoredAtom4157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08424
  ] at hbad
  tauto

theorem fin15Anchored_clause25579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1371 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom4158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16616
  ] at hbad
  tauto

theorem fin15Anchored_clause25580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1378 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1378 Fin15AnchoredAtom4158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16616
  ] at hbad
  tauto

theorem fin15Anchored_clause25581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1385 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1385 Fin15AnchoredAtom4158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16616
  ] at hbad
  tauto

theorem fin15Anchored_clause25582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1413 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1413 Fin15AnchoredAtom4158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16616
  ] at hbad
  tauto

theorem fin15Anchored_clause25583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4158 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom4158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16616
  ] at hbad
  tauto

theorem fin15Anchored_clause25584 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4158 chi ∧
      Fin15AnchoredAtom1371 chi ∧
      Fin15AnchoredAtom1378 chi ∧
      Fin15AnchoredAtom1385 chi ∧
      Fin15AnchoredAtom1413 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1371 Fin15AnchoredAtom1378 Fin15AnchoredAtom1385
    Fin15AnchoredAtom1413 Fin15AnchoredAtom1617 Fin15AnchoredAtom4158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16616
  ] at hbad
  tauto

theorem fin15Anchored_clause25585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom4159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00872
  ] at hbad
  tauto

theorem fin15Anchored_clause25586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1373 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1373 Fin15AnchoredAtom4159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00872
  ] at hbad
  tauto

theorem fin15Anchored_clause25587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1386 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1386 Fin15AnchoredAtom4159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00872
  ] at hbad
  tauto

theorem fin15Anchored_clause25588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1414 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1414 Fin15AnchoredAtom4159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00872
  ] at hbad
  tauto

theorem fin15Anchored_clause25589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4159 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom4159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00872
  ] at hbad
  tauto

theorem fin15Anchored_clause25590 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4159 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1373 chi ∧
      Fin15AnchoredAtom1386 chi ∧
      Fin15AnchoredAtom1414 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom1373 Fin15AnchoredAtom1386
    Fin15AnchoredAtom1414 Fin15AnchoredAtom1618 Fin15AnchoredAtom4159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00872
  ] at hbad
  tauto

theorem fin15Anchored_clause25591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom4160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01384
  ] at hbad
  tauto

theorem fin15Anchored_clause25592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1374 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1374 Fin15AnchoredAtom4160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01384
  ] at hbad
  tauto

theorem fin15Anchored_clause25593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1387 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1387 Fin15AnchoredAtom4160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01384
  ] at hbad
  tauto

theorem fin15Anchored_clause25594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1415 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1415 Fin15AnchoredAtom4160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01384
  ] at hbad
  tauto

theorem fin15Anchored_clause25595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4160 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom4160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01384
  ] at hbad
  tauto

theorem fin15Anchored_clause25596 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4160 chi ∧
      Fin15AnchoredAtom1372 chi ∧
      Fin15AnchoredAtom1374 chi ∧
      Fin15AnchoredAtom1387 chi ∧
      Fin15AnchoredAtom1415 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom1374 Fin15AnchoredAtom1387
    Fin15AnchoredAtom1415 Fin15AnchoredAtom1619 Fin15AnchoredAtom4160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01384
  ] at hbad
  tauto

theorem fin15Anchored_clause25597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom1372 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1372 Fin15AnchoredAtom4162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04456
  ] at hbad
  tauto

theorem fin15Anchored_clause25598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom1376 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1376 Fin15AnchoredAtom4162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04456
  ] at hbad
  tauto

theorem fin15Anchored_clause25599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4162 chi ∧
      ¬Fin15AnchoredAtom1417 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1417 Fin15AnchoredAtom4162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04456
  ] at hbad
  tauto

end ErdosSzekeres

end
