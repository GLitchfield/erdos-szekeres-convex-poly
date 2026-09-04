module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 207. -/

theorem fin15Anchored_clause26496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom4387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12400
  ] at hbad
  tauto

theorem fin15Anchored_clause26497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom4387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12400
  ] at hbad
  tauto

theorem fin15Anchored_clause26498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4387 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom4387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12400
  ] at hbad
  tauto

theorem fin15Anchored_clause26499 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4387 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom1497 Fin15AnchoredAtom1524
    Fin15AnchoredAtom1552 Fin15AnchoredAtom1636 Fin15AnchoredAtom4387 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12400
  ] at hbad
  tauto

theorem fin15Anchored_clause26500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom4388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20592
  ] at hbad
  tauto

theorem fin15Anchored_clause26501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom4388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20592
  ] at hbad
  tauto

theorem fin15Anchored_clause26502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom4388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20592
  ] at hbad
  tauto

theorem fin15Anchored_clause26503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom4388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20592
  ] at hbad
  tauto

theorem fin15Anchored_clause26504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4388 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom4388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20592
  ] at hbad
  tauto

theorem fin15Anchored_clause26505 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4388 chi ∧
      Fin15AnchoredAtom1496 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1496 Fin15AnchoredAtom1498 Fin15AnchoredAtom1525
    Fin15AnchoredAtom1553 Fin15AnchoredAtom1637 Fin15AnchoredAtom4388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20592
  ] at hbad
  tauto

theorem fin15Anchored_clause26506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom4389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24688
  ] at hbad
  tauto

theorem fin15Anchored_clause26507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1498 Fin15AnchoredAtom4389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24688
  ] at hbad
  tauto

theorem fin15Anchored_clause26508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom4389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24688
  ] at hbad
  tauto

theorem fin15Anchored_clause26509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom4389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24688
  ] at hbad
  tauto

theorem fin15Anchored_clause26510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4389 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom4389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24688
  ] at hbad
  tauto

theorem fin15Anchored_clause26511 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4389 chi ∧
      Fin15AnchoredAtom1497 chi ∧
      Fin15AnchoredAtom1498 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1497 Fin15AnchoredAtom1498 Fin15AnchoredAtom1526
    Fin15AnchoredAtom1554 Fin15AnchoredAtom1638 Fin15AnchoredAtom4389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24688
  ] at hbad
  tauto

theorem fin15Anchored_clause26512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom4390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00944
  ] at hbad
  tauto

theorem fin15Anchored_clause26513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom4390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00944
  ] at hbad
  tauto

theorem fin15Anchored_clause26514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom4390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00944
  ] at hbad
  tauto

theorem fin15Anchored_clause26515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom4390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00944
  ] at hbad
  tauto

theorem fin15Anchored_clause26516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4390 chi ∧
      ¬Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1639 Fin15AnchoredAtom4390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00944
  ] at hbad
  tauto

theorem fin15Anchored_clause26517 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4390 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1639 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom1500 Fin15AnchoredAtom1506
    Fin15AnchoredAtom1555 Fin15AnchoredAtom1639 Fin15AnchoredAtom4390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00944
  ] at hbad
  tauto

theorem fin15Anchored_clause26518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom4391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01456
  ] at hbad
  tauto

theorem fin15Anchored_clause26519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom4391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01456
  ] at hbad
  tauto

theorem fin15Anchored_clause26520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom4391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01456
  ] at hbad
  tauto

theorem fin15Anchored_clause26521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom4391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01456
  ] at hbad
  tauto

theorem fin15Anchored_clause26522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4391 chi ∧
      ¬Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1640 Fin15AnchoredAtom4391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01456
  ] at hbad
  tauto

theorem fin15Anchored_clause26523 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4391 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1640 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom1501 Fin15AnchoredAtom1507
    Fin15AnchoredAtom1556 Fin15AnchoredAtom1640 Fin15AnchoredAtom4391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01456
  ] at hbad
  tauto

theorem fin15Anchored_clause26524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom4393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04528
  ] at hbad
  tauto

theorem fin15Anchored_clause26525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom4393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04528
  ] at hbad
  tauto

theorem fin15Anchored_clause26526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1509 Fin15AnchoredAtom4393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04528
  ] at hbad
  tauto

theorem fin15Anchored_clause26527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom4393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04528
  ] at hbad
  tauto

theorem fin15Anchored_clause26528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4393 chi ∧
      ¬Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1642 Fin15AnchoredAtom4393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04528
  ] at hbad
  tauto

theorem fin15Anchored_clause26529 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4393 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1509 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1642 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom1503 Fin15AnchoredAtom1509
    Fin15AnchoredAtom1558 Fin15AnchoredAtom1642 Fin15AnchoredAtom4393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04528
  ] at hbad
  tauto

theorem fin15Anchored_clause26530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom4394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08624
  ] at hbad
  tauto

theorem fin15Anchored_clause26531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom4394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08624
  ] at hbad
  tauto

theorem fin15Anchored_clause26532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1510 Fin15AnchoredAtom4394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08624
  ] at hbad
  tauto

theorem fin15Anchored_clause26533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom4394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08624
  ] at hbad
  tauto

theorem fin15Anchored_clause26534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4394 chi ∧
      ¬Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1643 Fin15AnchoredAtom4394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08624
  ] at hbad
  tauto

theorem fin15Anchored_clause26535 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4394 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1510 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1643 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom1504 Fin15AnchoredAtom1510
    Fin15AnchoredAtom1559 Fin15AnchoredAtom1643 Fin15AnchoredAtom4394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08624
  ] at hbad
  tauto

theorem fin15Anchored_clause26536 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom4395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16816
  ] at hbad
  tauto

theorem fin15Anchored_clause26537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom4395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16816
  ] at hbad
  tauto

theorem fin15Anchored_clause26538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1511 Fin15AnchoredAtom4395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16816
  ] at hbad
  tauto

theorem fin15Anchored_clause26539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom4395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16816
  ] at hbad
  tauto

theorem fin15Anchored_clause26540 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4395 chi ∧
      ¬Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1644 Fin15AnchoredAtom4395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16816
  ] at hbad
  tauto

theorem fin15Anchored_clause26541 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4395 chi ∧
      Fin15AnchoredAtom1499 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1511 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1644 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1499 Fin15AnchoredAtom1505 Fin15AnchoredAtom1511
    Fin15AnchoredAtom1560 Fin15AnchoredAtom1644 Fin15AnchoredAtom4395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16816
  ] at hbad
  tauto

theorem fin15Anchored_clause26542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom4396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01712
  ] at hbad
  tauto

theorem fin15Anchored_clause26543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom4396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01712
  ] at hbad
  tauto

theorem fin15Anchored_clause26544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom4396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01712
  ] at hbad
  tauto

theorem fin15Anchored_clause26545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom4396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01712
  ] at hbad
  tauto

theorem fin15Anchored_clause26546 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4396 chi ∧
      ¬Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1645 Fin15AnchoredAtom4396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01712
  ] at hbad
  tauto

theorem fin15Anchored_clause26547 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4396 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1645 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom1501 Fin15AnchoredAtom1512
    Fin15AnchoredAtom1561 Fin15AnchoredAtom1645 Fin15AnchoredAtom4396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01712
  ] at hbad
  tauto

theorem fin15Anchored_clause26548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom4397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02736
  ] at hbad
  tauto

theorem fin15Anchored_clause26549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1502 Fin15AnchoredAtom4397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02736
  ] at hbad
  tauto

theorem fin15Anchored_clause26550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4397 chi ∧
      ¬Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1646 Fin15AnchoredAtom4397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02736
  ] at hbad
  tauto

theorem fin15Anchored_clause26551 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4397 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1502 chi ∧
      Fin15AnchoredAtom1513 chi ∧
      Fin15AnchoredAtom1562 chi ∧
      Fin15AnchoredAtom1646 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom1502 Fin15AnchoredAtom1513
    Fin15AnchoredAtom1562 Fin15AnchoredAtom1646 Fin15AnchoredAtom4397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02736
  ] at hbad
  tauto

theorem fin15Anchored_clause26552 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom4398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04784
  ] at hbad
  tauto

theorem fin15Anchored_clause26553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom4398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04784
  ] at hbad
  tauto

theorem fin15Anchored_clause26554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1514 Fin15AnchoredAtom4398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04784
  ] at hbad
  tauto

theorem fin15Anchored_clause26555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom4398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04784
  ] at hbad
  tauto

theorem fin15Anchored_clause26556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4398 chi ∧
      ¬Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1647 Fin15AnchoredAtom4398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04784
  ] at hbad
  tauto

theorem fin15Anchored_clause26557 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4398 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1514 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1647 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom1503 Fin15AnchoredAtom1514
    Fin15AnchoredAtom1563 Fin15AnchoredAtom1647 Fin15AnchoredAtom4398 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04784
  ] at hbad
  tauto

theorem fin15Anchored_clause26558 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom4399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08880
  ] at hbad
  tauto

theorem fin15Anchored_clause26559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom4399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08880
  ] at hbad
  tauto

theorem fin15Anchored_clause26560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1515 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1515 Fin15AnchoredAtom4399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08880
  ] at hbad
  tauto

theorem fin15Anchored_clause26561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom4399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08880
  ] at hbad
  tauto

theorem fin15Anchored_clause26562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4399 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom4399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08880
  ] at hbad
  tauto

theorem fin15Anchored_clause26563 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4399 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1515 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom1504 Fin15AnchoredAtom1515
    Fin15AnchoredAtom1564 Fin15AnchoredAtom1648 Fin15AnchoredAtom4399 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08880
  ] at hbad
  tauto

theorem fin15Anchored_clause26564 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom4400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17072
  ] at hbad
  tauto

theorem fin15Anchored_clause26565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom4400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17072
  ] at hbad
  tauto

theorem fin15Anchored_clause26566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1516 Fin15AnchoredAtom4400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17072
  ] at hbad
  tauto

theorem fin15Anchored_clause26567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom4400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17072
  ] at hbad
  tauto

theorem fin15Anchored_clause26568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4400 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom4400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17072
  ] at hbad
  tauto

theorem fin15Anchored_clause26569 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4400 chi ∧
      Fin15AnchoredAtom1500 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1516 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1500 Fin15AnchoredAtom1505 Fin15AnchoredAtom1516
    Fin15AnchoredAtom1565 Fin15AnchoredAtom1649 Fin15AnchoredAtom4400 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17072
  ] at hbad
  tauto

theorem fin15Anchored_clause26570 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom4401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03248
  ] at hbad
  tauto

theorem fin15Anchored_clause26571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1502 Fin15AnchoredAtom4401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03248
  ] at hbad
  tauto

theorem fin15Anchored_clause26572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1566 Fin15AnchoredAtom4401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03248
  ] at hbad
  tauto

theorem fin15Anchored_clause26573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4401 chi ∧
      ¬Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1650 Fin15AnchoredAtom4401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03248
  ] at hbad
  tauto

theorem fin15Anchored_clause26574 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4401 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1502 chi ∧
      Fin15AnchoredAtom1517 chi ∧
      Fin15AnchoredAtom1566 chi ∧
      Fin15AnchoredAtom1650 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom1502 Fin15AnchoredAtom1517
    Fin15AnchoredAtom1566 Fin15AnchoredAtom1650 Fin15AnchoredAtom4401 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03248
  ] at hbad
  tauto

theorem fin15Anchored_clause26575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom4402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05296
  ] at hbad
  tauto

theorem fin15Anchored_clause26576 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom4402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05296
  ] at hbad
  tauto

theorem fin15Anchored_clause26577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1518 Fin15AnchoredAtom4402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05296
  ] at hbad
  tauto

theorem fin15Anchored_clause26578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom4402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05296
  ] at hbad
  tauto

theorem fin15Anchored_clause26579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4402 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom4402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05296
  ] at hbad
  tauto

theorem fin15Anchored_clause26580 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4402 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1518 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom1503 Fin15AnchoredAtom1518
    Fin15AnchoredAtom1567 Fin15AnchoredAtom1651 Fin15AnchoredAtom4402 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05296
  ] at hbad
  tauto

theorem fin15Anchored_clause26581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom4403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09392
  ] at hbad
  tauto

theorem fin15Anchored_clause26582 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom4403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09392
  ] at hbad
  tauto

theorem fin15Anchored_clause26583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1519 Fin15AnchoredAtom4403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09392
  ] at hbad
  tauto

theorem fin15Anchored_clause26584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom4403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09392
  ] at hbad
  tauto

theorem fin15Anchored_clause26585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4403 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom4403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09392
  ] at hbad
  tauto

theorem fin15Anchored_clause26586 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4403 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1519 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom1504 Fin15AnchoredAtom1519
    Fin15AnchoredAtom1568 Fin15AnchoredAtom1652 Fin15AnchoredAtom4403 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09392
  ] at hbad
  tauto

theorem fin15Anchored_clause26587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom4404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17584
  ] at hbad
  tauto

theorem fin15Anchored_clause26588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom4404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17584
  ] at hbad
  tauto

theorem fin15Anchored_clause26589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1520 Fin15AnchoredAtom4404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17584
  ] at hbad
  tauto

theorem fin15Anchored_clause26590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom4404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17584
  ] at hbad
  tauto

theorem fin15Anchored_clause26591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4404 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom4404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17584
  ] at hbad
  tauto

theorem fin15Anchored_clause26592 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4404 chi ∧
      Fin15AnchoredAtom1501 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1520 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1501 Fin15AnchoredAtom1505 Fin15AnchoredAtom1520
    Fin15AnchoredAtom1569 Fin15AnchoredAtom1653 Fin15AnchoredAtom4404 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17584
  ] at hbad
  tauto

theorem fin15Anchored_clause26593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom4405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06320
  ] at hbad
  tauto

theorem fin15Anchored_clause26594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4405 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1654 Fin15AnchoredAtom4405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06320
  ] at hbad
  tauto

theorem fin15Anchored_clause26595 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4405 chi ∧
      Fin15AnchoredAtom1502 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1521 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1502 Fin15AnchoredAtom1503 Fin15AnchoredAtom1521
    Fin15AnchoredAtom1570 Fin15AnchoredAtom1654 Fin15AnchoredAtom4405 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06320
  ] at hbad
  tauto

theorem fin15Anchored_clause26596 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom1502 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1502 Fin15AnchoredAtom4406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10416
  ] at hbad
  tauto

theorem fin15Anchored_clause26597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4406 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom4406 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10416
  ] at hbad
  tauto

theorem fin15Anchored_clause26598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4407 chi ∧
      ¬Fin15AnchoredAtom1656 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1656 Fin15AnchoredAtom4407 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18608
  ] at hbad
  tauto

theorem fin15Anchored_clause26599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom4408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12464
  ] at hbad
  tauto

theorem fin15Anchored_clause26600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom4408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12464
  ] at hbad
  tauto

theorem fin15Anchored_clause26601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1524 Fin15AnchoredAtom4408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12464
  ] at hbad
  tauto

theorem fin15Anchored_clause26602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom4408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12464
  ] at hbad
  tauto

theorem fin15Anchored_clause26603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4408 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom4408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12464
  ] at hbad
  tauto

theorem fin15Anchored_clause26604 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4408 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1524 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom1504 Fin15AnchoredAtom1524
    Fin15AnchoredAtom1573 Fin15AnchoredAtom1657 Fin15AnchoredAtom4408 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12464
  ] at hbad
  tauto

theorem fin15Anchored_clause26605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom4409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20656
  ] at hbad
  tauto

theorem fin15Anchored_clause26606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom4409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20656
  ] at hbad
  tauto

theorem fin15Anchored_clause26607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1525 Fin15AnchoredAtom4409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20656
  ] at hbad
  tauto

theorem fin15Anchored_clause26608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom4409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20656
  ] at hbad
  tauto

theorem fin15Anchored_clause26609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4409 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom4409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20656
  ] at hbad
  tauto

theorem fin15Anchored_clause26610 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4409 chi ∧
      Fin15AnchoredAtom1503 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1525 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1503 Fin15AnchoredAtom1505 Fin15AnchoredAtom1525
    Fin15AnchoredAtom1574 Fin15AnchoredAtom1658 Fin15AnchoredAtom4409 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20656
  ] at hbad
  tauto

theorem fin15Anchored_clause26611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom4410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24752
  ] at hbad
  tauto

theorem fin15Anchored_clause26612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1505 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1505 Fin15AnchoredAtom4410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24752
  ] at hbad
  tauto

theorem fin15Anchored_clause26613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1526 Fin15AnchoredAtom4410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24752
  ] at hbad
  tauto

theorem fin15Anchored_clause26614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom4410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24752
  ] at hbad
  tauto

theorem fin15Anchored_clause26615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4410 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom4410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24752
  ] at hbad
  tauto

theorem fin15Anchored_clause26616 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4410 chi ∧
      Fin15AnchoredAtom1504 chi ∧
      Fin15AnchoredAtom1505 chi ∧
      Fin15AnchoredAtom1526 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1504 Fin15AnchoredAtom1505 Fin15AnchoredAtom1526
    Fin15AnchoredAtom1575 Fin15AnchoredAtom1659 Fin15AnchoredAtom4410 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24752
  ] at hbad
  tauto

theorem fin15Anchored_clause26617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom4411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01840
  ] at hbad
  tauto

theorem fin15Anchored_clause26618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1507 Fin15AnchoredAtom4411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01840
  ] at hbad
  tauto

theorem fin15Anchored_clause26619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1512 Fin15AnchoredAtom4411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01840
  ] at hbad
  tauto

theorem fin15Anchored_clause26620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom4411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01840
  ] at hbad
  tauto

theorem fin15Anchored_clause26621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4411 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom4411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01840
  ] at hbad
  tauto

theorem fin15Anchored_clause26622 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4411 chi ∧
      Fin15AnchoredAtom1506 chi ∧
      Fin15AnchoredAtom1507 chi ∧
      Fin15AnchoredAtom1512 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom1507 Fin15AnchoredAtom1512
    Fin15AnchoredAtom1576 Fin15AnchoredAtom1660 Fin15AnchoredAtom4411 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01840
  ] at hbad
  tauto

theorem fin15Anchored_clause26623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4413 chi ∧
      ¬Fin15AnchoredAtom1506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1506 Fin15AnchoredAtom4413 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04912
  ] at hbad
  tauto

end ErdosSzekeres

end
