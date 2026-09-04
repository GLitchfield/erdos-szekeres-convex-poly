module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 206. -/

theorem fin15Anchored_clause26368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom4360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29704
  ] at hbad
  tauto

theorem fin15Anchored_clause26369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1485 Fin15AnchoredAtom4360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29704
  ] at hbad
  tauto

theorem fin15Anchored_clause26370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1486 Fin15AnchoredAtom4360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29704
  ] at hbad
  tauto

theorem fin15Anchored_clause26371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1490 Fin15AnchoredAtom4360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29704
  ] at hbad
  tauto

theorem fin15Anchored_clause26372 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4360 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom4360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29704
  ] at hbad
  tauto

theorem fin15Anchored_clause26373 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4360 chi ∧
      Fin15AnchoredAtom1484 chi ∧
      Fin15AnchoredAtom1485 chi ∧
      Fin15AnchoredAtom1486 chi ∧
      Fin15AnchoredAtom1490 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1484 Fin15AnchoredAtom1485 Fin15AnchoredAtom1486
    Fin15AnchoredAtom1490 Fin15AnchoredAtom1819 Fin15AnchoredAtom4360 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29704
  ] at hbad
  tauto

theorem fin15Anchored_clause26374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom4362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00496
  ] at hbad
  tauto

theorem fin15Anchored_clause26375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom4362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00496
  ] at hbad
  tauto

theorem fin15Anchored_clause26376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom4362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00496
  ] at hbad
  tauto

theorem fin15Anchored_clause26377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1527 Fin15AnchoredAtom4362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00496
  ] at hbad
  tauto

theorem fin15Anchored_clause26378 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4362 chi ∧
      ¬Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1611 Fin15AnchoredAtom4362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00496
  ] at hbad
  tauto

theorem fin15Anchored_clause26379 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4362 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1527 chi ∧
      Fin15AnchoredAtom1611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom1492 Fin15AnchoredAtom1499
    Fin15AnchoredAtom1527 Fin15AnchoredAtom1611 Fin15AnchoredAtom4362 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00496
  ] at hbad
  tauto

theorem fin15Anchored_clause26380 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom4363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00752
  ] at hbad
  tauto

theorem fin15Anchored_clause26381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom4363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00752
  ] at hbad
  tauto

theorem fin15Anchored_clause26382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom4363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00752
  ] at hbad
  tauto

theorem fin15Anchored_clause26383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1528 Fin15AnchoredAtom4363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00752
  ] at hbad
  tauto

theorem fin15Anchored_clause26384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4363 chi ∧
      ¬Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1612 Fin15AnchoredAtom4363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00752
  ] at hbad
  tauto

theorem fin15Anchored_clause26385 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4363 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1528 chi ∧
      Fin15AnchoredAtom1612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom1493 Fin15AnchoredAtom1500
    Fin15AnchoredAtom1528 Fin15AnchoredAtom1612 Fin15AnchoredAtom4363 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00752
  ] at hbad
  tauto

theorem fin15Anchored_clause26386 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom4364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01264
  ] at hbad
  tauto

theorem fin15Anchored_clause26387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom4364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01264
  ] at hbad
  tauto

theorem fin15Anchored_clause26388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom4364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01264
  ] at hbad
  tauto

theorem fin15Anchored_clause26389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1529 Fin15AnchoredAtom4364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01264
  ] at hbad
  tauto

theorem fin15Anchored_clause26390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4364 chi ∧
      ¬Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1613 Fin15AnchoredAtom4364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01264
  ] at hbad
  tauto

theorem fin15Anchored_clause26391 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4364 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1529 chi ∧
      Fin15AnchoredAtom1613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom1494 Fin15AnchoredAtom1501
    Fin15AnchoredAtom1529 Fin15AnchoredAtom1613 Fin15AnchoredAtom4364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01264
  ] at hbad
  tauto

theorem fin15Anchored_clause26392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1502 Fin15AnchoredAtom4365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02288
  ] at hbad
  tauto

theorem fin15Anchored_clause26393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4365 chi ∧
      ¬Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1614 Fin15AnchoredAtom4365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02288
  ] at hbad
  tauto

theorem fin15Anchored_clause26394 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4365 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1495 chi ∧
      Fin15AnchoredAtom1502 chi ∧
      Fin15AnchoredAtom1530 chi ∧
      Fin15AnchoredAtom1614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom1495 Fin15AnchoredAtom1502
    Fin15AnchoredAtom1530 Fin15AnchoredAtom1614 Fin15AnchoredAtom4365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02288
  ] at hbad
  tauto

theorem fin15Anchored_clause26395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom4366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04336
  ] at hbad
  tauto

theorem fin15Anchored_clause26396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom4366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04336
  ] at hbad
  tauto

theorem fin15Anchored_clause26397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom4366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04336
  ] at hbad
  tauto

theorem fin15Anchored_clause26398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1531 Fin15AnchoredAtom4366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04336
  ] at hbad
  tauto

theorem fin15Anchored_clause26399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4366 chi ∧
      ¬Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1615 Fin15AnchoredAtom4366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04336
  ] at hbad
  tauto

theorem fin15Anchored_clause26400 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4366 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1531 chi ∧
      Fin15AnchoredAtom1615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom1496 Fin15AnchoredAtom1503
    Fin15AnchoredAtom1531 Fin15AnchoredAtom1615 Fin15AnchoredAtom4366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04336
  ] at hbad
  tauto

theorem fin15Anchored_clause26401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom4367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08432
  ] at hbad
  tauto

theorem fin15Anchored_clause26402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom4367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08432
  ] at hbad
  tauto

theorem fin15Anchored_clause26403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom4367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08432
  ] at hbad
  tauto

theorem fin15Anchored_clause26404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1532 Fin15AnchoredAtom4367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08432
  ] at hbad
  tauto

theorem fin15Anchored_clause26405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4367 chi ∧
      ¬Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1616 Fin15AnchoredAtom4367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08432
  ] at hbad
  tauto

theorem fin15Anchored_clause26406 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4367 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1532 chi ∧
      Fin15AnchoredAtom1616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom1497 Fin15AnchoredAtom1504
    Fin15AnchoredAtom1532 Fin15AnchoredAtom1616 Fin15AnchoredAtom4367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08432
  ] at hbad
  tauto

theorem fin15Anchored_clause26407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom4368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16624
  ] at hbad
  tauto

theorem fin15Anchored_clause26408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom4368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16624
  ] at hbad
  tauto

theorem fin15Anchored_clause26409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom4368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16624
  ] at hbad
  tauto

theorem fin15Anchored_clause26410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1533 Fin15AnchoredAtom4368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16624
  ] at hbad
  tauto

theorem fin15Anchored_clause26411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4368 chi ∧
      ¬Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1617 Fin15AnchoredAtom4368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16624
  ] at hbad
  tauto

theorem fin15Anchored_clause26412 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4368 chi ∧
      Fin15AnchoredAtom1491 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1533 chi ∧
      Fin15AnchoredAtom1617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1491 Fin15AnchoredAtom1498 Fin15AnchoredAtom1505
    Fin15AnchoredAtom1533 Fin15AnchoredAtom1617 Fin15AnchoredAtom4368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16624
  ] at hbad
  tauto

theorem fin15Anchored_clause26413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom4369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00880
  ] at hbad
  tauto

theorem fin15Anchored_clause26414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom4369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00880
  ] at hbad
  tauto

theorem fin15Anchored_clause26415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom4369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00880
  ] at hbad
  tauto

theorem fin15Anchored_clause26416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom4369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00880
  ] at hbad
  tauto

theorem fin15Anchored_clause26417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4369 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom4369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00880
  ] at hbad
  tauto

theorem fin15Anchored_clause26418 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4369 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom1493 Fin15AnchoredAtom1506
    Fin15AnchoredAtom1534 Fin15AnchoredAtom1618 Fin15AnchoredAtom4369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00880
  ] at hbad
  tauto

theorem fin15Anchored_clause26419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom4370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01392
  ] at hbad
  tauto

theorem fin15Anchored_clause26420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom4370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01392
  ] at hbad
  tauto

theorem fin15Anchored_clause26421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom4370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01392
  ] at hbad
  tauto

theorem fin15Anchored_clause26422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom4370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01392
  ] at hbad
  tauto

theorem fin15Anchored_clause26423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4370 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom4370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01392
  ] at hbad
  tauto

theorem fin15Anchored_clause26424 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4370 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom1494 Fin15AnchoredAtom1507
    Fin15AnchoredAtom1535 Fin15AnchoredAtom1619 Fin15AnchoredAtom4370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01392
  ] at hbad
  tauto

theorem fin15Anchored_clause26425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom4372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04464
  ] at hbad
  tauto

theorem fin15Anchored_clause26426 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom4372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04464
  ] at hbad
  tauto

theorem fin15Anchored_clause26427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom4372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04464
  ] at hbad
  tauto

theorem fin15Anchored_clause26428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom4372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04464
  ] at hbad
  tauto

theorem fin15Anchored_clause26429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4372 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom4372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04464
  ] at hbad
  tauto

theorem fin15Anchored_clause26430 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4372 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom1496 Fin15AnchoredAtom1509
    Fin15AnchoredAtom1537 Fin15AnchoredAtom1621 Fin15AnchoredAtom4372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04464
  ] at hbad
  tauto

theorem fin15Anchored_clause26431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom4373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08560
  ] at hbad
  tauto

theorem fin15Anchored_clause26432 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom4373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08560
  ] at hbad
  tauto

theorem fin15Anchored_clause26433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom4373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08560
  ] at hbad
  tauto

theorem fin15Anchored_clause26434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1538 Fin15AnchoredAtom4373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08560
  ] at hbad
  tauto

theorem fin15Anchored_clause26435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4373 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom4373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08560
  ] at hbad
  tauto

theorem fin15Anchored_clause26436 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4373 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom1497 Fin15AnchoredAtom1510
    Fin15AnchoredAtom1538 Fin15AnchoredAtom1622 Fin15AnchoredAtom4373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08560
  ] at hbad
  tauto

theorem fin15Anchored_clause26437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom4374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16752
  ] at hbad
  tauto

theorem fin15Anchored_clause26438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom4374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16752
  ] at hbad
  tauto

theorem fin15Anchored_clause26439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1511 Fin15AnchoredAtom4374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16752
  ] at hbad
  tauto

theorem fin15Anchored_clause26440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1539 Fin15AnchoredAtom4374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16752
  ] at hbad
  tauto

theorem fin15Anchored_clause26441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4374 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1623 Fin15AnchoredAtom4374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16752
  ] at hbad
  tauto

theorem fin15Anchored_clause26442 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4374 chi ∧
      Fin15AnchoredAtom1492 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1492 Fin15AnchoredAtom1498 Fin15AnchoredAtom1511
    Fin15AnchoredAtom1539 Fin15AnchoredAtom1623 Fin15AnchoredAtom4374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16752
  ] at hbad
  tauto

theorem fin15Anchored_clause26443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom4375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01648
  ] at hbad
  tauto

theorem fin15Anchored_clause26444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom4375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01648
  ] at hbad
  tauto

theorem fin15Anchored_clause26445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom4375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01648
  ] at hbad
  tauto

theorem fin15Anchored_clause26446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom4375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01648
  ] at hbad
  tauto

theorem fin15Anchored_clause26447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4375 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom4375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01648
  ] at hbad
  tauto

theorem fin15Anchored_clause26448 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4375 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom1494 Fin15AnchoredAtom1512
    Fin15AnchoredAtom1540 Fin15AnchoredAtom1624 Fin15AnchoredAtom4375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01648
  ] at hbad
  tauto

theorem fin15Anchored_clause26449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4376 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom4376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02672
  ] at hbad
  tauto

theorem fin15Anchored_clause26450 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4376 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1495 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1541 chi ∧
      Fin15AnchoredAtom1625 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom1495 Fin15AnchoredAtom1513
    Fin15AnchoredAtom1541 Fin15AnchoredAtom1625 Fin15AnchoredAtom4376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02672
  ] at hbad
  tauto

theorem fin15Anchored_clause26451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom4377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04720
  ] at hbad
  tauto

theorem fin15Anchored_clause26452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom4377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04720
  ] at hbad
  tauto

theorem fin15Anchored_clause26453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom4377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04720
  ] at hbad
  tauto

theorem fin15Anchored_clause26454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom4377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04720
  ] at hbad
  tauto

theorem fin15Anchored_clause26455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4377 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom4377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04720
  ] at hbad
  tauto

theorem fin15Anchored_clause26456 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4377 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom1496 Fin15AnchoredAtom1514
    Fin15AnchoredAtom1542 Fin15AnchoredAtom1626 Fin15AnchoredAtom4377 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04720
  ] at hbad
  tauto

theorem fin15Anchored_clause26457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom4378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08816
  ] at hbad
  tauto

theorem fin15Anchored_clause26458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom4378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08816
  ] at hbad
  tauto

theorem fin15Anchored_clause26459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom4378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08816
  ] at hbad
  tauto

theorem fin15Anchored_clause26460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom4378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08816
  ] at hbad
  tauto

theorem fin15Anchored_clause26461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4378 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom4378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08816
  ] at hbad
  tauto

theorem fin15Anchored_clause26462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4378 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom1497 Fin15AnchoredAtom1515
    Fin15AnchoredAtom1543 Fin15AnchoredAtom1627 Fin15AnchoredAtom4378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08816
  ] at hbad
  tauto

theorem fin15Anchored_clause26463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom4379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17008
  ] at hbad
  tauto

theorem fin15Anchored_clause26464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom4379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17008
  ] at hbad
  tauto

theorem fin15Anchored_clause26465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom4379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17008
  ] at hbad
  tauto

theorem fin15Anchored_clause26466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom4379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17008
  ] at hbad
  tauto

theorem fin15Anchored_clause26467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4379 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom4379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17008
  ] at hbad
  tauto

theorem fin15Anchored_clause26468 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4379 chi ∧
      Fin15AnchoredAtom1493 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1493 Fin15AnchoredAtom1498 Fin15AnchoredAtom1516
    Fin15AnchoredAtom1544 Fin15AnchoredAtom1628 Fin15AnchoredAtom4379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17008
  ] at hbad
  tauto

theorem fin15Anchored_clause26469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4380 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom4380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03184
  ] at hbad
  tauto

theorem fin15Anchored_clause26470 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4380 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1495 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1545 chi ∧
      Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom1495 Fin15AnchoredAtom1517
    Fin15AnchoredAtom1545 Fin15AnchoredAtom1629 Fin15AnchoredAtom4380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03184
  ] at hbad
  tauto

theorem fin15Anchored_clause26471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom4381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05232
  ] at hbad
  tauto

theorem fin15Anchored_clause26472 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom4381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05232
  ] at hbad
  tauto

theorem fin15Anchored_clause26473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom4381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05232
  ] at hbad
  tauto

theorem fin15Anchored_clause26474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom4381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05232
  ] at hbad
  tauto

theorem fin15Anchored_clause26475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4381 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom4381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05232
  ] at hbad
  tauto

theorem fin15Anchored_clause26476 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4381 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom1496 Fin15AnchoredAtom1518
    Fin15AnchoredAtom1546 Fin15AnchoredAtom1630 Fin15AnchoredAtom4381 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05232
  ] at hbad
  tauto

theorem fin15Anchored_clause26477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom4382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09328
  ] at hbad
  tauto

theorem fin15Anchored_clause26478 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom4382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09328
  ] at hbad
  tauto

theorem fin15Anchored_clause26479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom4382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09328
  ] at hbad
  tauto

theorem fin15Anchored_clause26480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom4382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09328
  ] at hbad
  tauto

theorem fin15Anchored_clause26481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4382 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom4382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09328
  ] at hbad
  tauto

theorem fin15Anchored_clause26482 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4382 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom1497 Fin15AnchoredAtom1519
    Fin15AnchoredAtom1547 Fin15AnchoredAtom1631 Fin15AnchoredAtom4382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09328
  ] at hbad
  tauto

theorem fin15Anchored_clause26483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1494 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom4383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17520
  ] at hbad
  tauto

theorem fin15Anchored_clause26484 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom4383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17520
  ] at hbad
  tauto

theorem fin15Anchored_clause26485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom4383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17520
  ] at hbad
  tauto

theorem fin15Anchored_clause26486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom4383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17520
  ] at hbad
  tauto

theorem fin15Anchored_clause26487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4383 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom4383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17520
  ] at hbad
  tauto

theorem fin15Anchored_clause26488 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4383 chi ∧
      Fin15AnchoredAtom1494 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1494 Fin15AnchoredAtom1498 Fin15AnchoredAtom1520
    Fin15AnchoredAtom1548 Fin15AnchoredAtom1632 Fin15AnchoredAtom4383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17520
  ] at hbad
  tauto

theorem fin15Anchored_clause26489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4384 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom4384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06256
  ] at hbad
  tauto

theorem fin15Anchored_clause26490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4384 chi ∧
      ¬Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1633 Fin15AnchoredAtom4384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06256
  ] at hbad
  tauto

theorem fin15Anchored_clause26491 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4384 chi ∧
      Fin15AnchoredAtom1495 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1549 chi ∧
      Fin15AnchoredAtom1633 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1495 Fin15AnchoredAtom1496 Fin15AnchoredAtom1521
    Fin15AnchoredAtom1549 Fin15AnchoredAtom1633 Fin15AnchoredAtom4384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06256
  ] at hbad
  tauto

theorem fin15Anchored_clause26492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4385 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom4385 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10352
  ] at hbad
  tauto

theorem fin15Anchored_clause26493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4386 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom4386 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18544
  ] at hbad
  tauto

theorem fin15Anchored_clause26494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom4387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12400
  ] at hbad
  tauto

theorem fin15Anchored_clause26495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom4387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12400
  ] at hbad
  tauto

end ErdosSzekeres

end
