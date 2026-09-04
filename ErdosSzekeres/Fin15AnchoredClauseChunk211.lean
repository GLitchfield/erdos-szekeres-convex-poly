module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 211. -/

theorem fin15Anchored_clause27008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4499 chi ∧
      ¬Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1549 Fin15AnchoredAtom4499 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22608
  ] at hbad
  tauto

theorem fin15Anchored_clause27009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4499 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom4499 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22608
  ] at hbad
  tauto

theorem fin15Anchored_clause27010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom4501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28752
  ] at hbad
  tauto

theorem fin15Anchored_clause27011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom4501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28752
  ] at hbad
  tauto

theorem fin15Anchored_clause27012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom4501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28752
  ] at hbad
  tauto

theorem fin15Anchored_clause27013 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1610 Fin15AnchoredAtom4501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28752
  ] at hbad
  tauto

theorem fin15Anchored_clause27014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4501 chi ∧
      ¬Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1750 Fin15AnchoredAtom4501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28752
  ] at hbad
  tauto

theorem fin15Anchored_clause27015 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4501 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1610 chi ∧
      Fin15AnchoredAtom1750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom1553 Fin15AnchoredAtom1554
    Fin15AnchoredAtom1610 Fin15AnchoredAtom1750 Fin15AnchoredAtom4501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28752
  ] at hbad
  tauto

theorem fin15Anchored_clause27016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom4502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01936
  ] at hbad
  tauto

theorem fin15Anchored_clause27017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom4502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01936
  ] at hbad
  tauto

theorem fin15Anchored_clause27018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom4502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01936
  ] at hbad
  tauto

theorem fin15Anchored_clause27019 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1576 Fin15AnchoredAtom4502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01936
  ] at hbad
  tauto

theorem fin15Anchored_clause27020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4502 chi ∧
      ¬Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1751 Fin15AnchoredAtom4502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01936
  ] at hbad
  tauto

theorem fin15Anchored_clause27021 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4502 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1576 chi ∧
      Fin15AnchoredAtom1751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom1556 Fin15AnchoredAtom1561
    Fin15AnchoredAtom1576 Fin15AnchoredAtom1751 Fin15AnchoredAtom4502 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01936
  ] at hbad
  tauto

theorem fin15Anchored_clause27022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom4504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05008
  ] at hbad
  tauto

theorem fin15Anchored_clause27023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom4504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05008
  ] at hbad
  tauto

theorem fin15Anchored_clause27024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom4504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05008
  ] at hbad
  tauto

theorem fin15Anchored_clause27025 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1578 Fin15AnchoredAtom4504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05008
  ] at hbad
  tauto

theorem fin15Anchored_clause27026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4504 chi ∧
      ¬Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1753 Fin15AnchoredAtom4504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05008
  ] at hbad
  tauto

theorem fin15Anchored_clause27027 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4504 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom1558 Fin15AnchoredAtom1563
    Fin15AnchoredAtom1578 Fin15AnchoredAtom1753 Fin15AnchoredAtom4504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05008
  ] at hbad
  tauto

theorem fin15Anchored_clause27028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom4505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09104
  ] at hbad
  tauto

theorem fin15Anchored_clause27029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom4505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09104
  ] at hbad
  tauto

theorem fin15Anchored_clause27030 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom4505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09104
  ] at hbad
  tauto

theorem fin15Anchored_clause27031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1579 Fin15AnchoredAtom4505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09104
  ] at hbad
  tauto

theorem fin15Anchored_clause27032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4505 chi ∧
      ¬Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1754 Fin15AnchoredAtom4505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09104
  ] at hbad
  tauto

theorem fin15Anchored_clause27033 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4505 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom1559 Fin15AnchoredAtom1564
    Fin15AnchoredAtom1579 Fin15AnchoredAtom1754 Fin15AnchoredAtom4505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09104
  ] at hbad
  tauto

theorem fin15Anchored_clause27034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom4506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17296
  ] at hbad
  tauto

theorem fin15Anchored_clause27035 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom4506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17296
  ] at hbad
  tauto

theorem fin15Anchored_clause27036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom4506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17296
  ] at hbad
  tauto

theorem fin15Anchored_clause27037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1580 Fin15AnchoredAtom4506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17296
  ] at hbad
  tauto

theorem fin15Anchored_clause27038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4506 chi ∧
      ¬Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1755 Fin15AnchoredAtom4506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17296
  ] at hbad
  tauto

theorem fin15Anchored_clause27039 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4506 chi ∧
      Fin15AnchoredAtom1555 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom1560 Fin15AnchoredAtom1565
    Fin15AnchoredAtom1580 Fin15AnchoredAtom1755 Fin15AnchoredAtom4506 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17296
  ] at hbad
  tauto

theorem fin15Anchored_clause27040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom4508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05520
  ] at hbad
  tauto

theorem fin15Anchored_clause27041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom4508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05520
  ] at hbad
  tauto

theorem fin15Anchored_clause27042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom4508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05520
  ] at hbad
  tauto

theorem fin15Anchored_clause27043 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom4508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05520
  ] at hbad
  tauto

theorem fin15Anchored_clause27044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4508 chi ∧
      ¬Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1757 Fin15AnchoredAtom4508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05520
  ] at hbad
  tauto

theorem fin15Anchored_clause27045 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4508 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom1558 Fin15AnchoredAtom1567
    Fin15AnchoredAtom1582 Fin15AnchoredAtom1757 Fin15AnchoredAtom4508 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05520
  ] at hbad
  tauto

theorem fin15Anchored_clause27046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom4509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09616
  ] at hbad
  tauto

theorem fin15Anchored_clause27047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom4509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09616
  ] at hbad
  tauto

theorem fin15Anchored_clause27048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom4509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09616
  ] at hbad
  tauto

theorem fin15Anchored_clause27049 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom4509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09616
  ] at hbad
  tauto

theorem fin15Anchored_clause27050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4509 chi ∧
      ¬Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1758 Fin15AnchoredAtom4509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09616
  ] at hbad
  tauto

theorem fin15Anchored_clause27051 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4509 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom1559 Fin15AnchoredAtom1568
    Fin15AnchoredAtom1583 Fin15AnchoredAtom1758 Fin15AnchoredAtom4509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09616
  ] at hbad
  tauto

theorem fin15Anchored_clause27052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom4510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17808
  ] at hbad
  tauto

theorem fin15Anchored_clause27053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom4510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17808
  ] at hbad
  tauto

theorem fin15Anchored_clause27054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom4510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17808
  ] at hbad
  tauto

theorem fin15Anchored_clause27055 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1584 Fin15AnchoredAtom4510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17808
  ] at hbad
  tauto

theorem fin15Anchored_clause27056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4510 chi ∧
      ¬Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1759 Fin15AnchoredAtom4510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17808
  ] at hbad
  tauto

theorem fin15Anchored_clause27057 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4510 chi ∧
      Fin15AnchoredAtom1556 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom1560 Fin15AnchoredAtom1569
    Fin15AnchoredAtom1584 Fin15AnchoredAtom1759 Fin15AnchoredAtom4510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17808
  ] at hbad
  tauto

theorem fin15Anchored_clause27058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom4514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12688
  ] at hbad
  tauto

theorem fin15Anchored_clause27059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom4514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12688
  ] at hbad
  tauto

theorem fin15Anchored_clause27060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom4514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12688
  ] at hbad
  tauto

theorem fin15Anchored_clause27061 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom4514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12688
  ] at hbad
  tauto

theorem fin15Anchored_clause27062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4514 chi ∧
      ¬Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1763 Fin15AnchoredAtom4514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12688
  ] at hbad
  tauto

theorem fin15Anchored_clause27063 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4514 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom1559 Fin15AnchoredAtom1573
    Fin15AnchoredAtom1588 Fin15AnchoredAtom1763 Fin15AnchoredAtom4514 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12688
  ] at hbad
  tauto

theorem fin15Anchored_clause27064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1558 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom4515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20880
  ] at hbad
  tauto

theorem fin15Anchored_clause27065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom4515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20880
  ] at hbad
  tauto

theorem fin15Anchored_clause27066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom4515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20880
  ] at hbad
  tauto

theorem fin15Anchored_clause27067 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1589 Fin15AnchoredAtom4515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20880
  ] at hbad
  tauto

theorem fin15Anchored_clause27068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4515 chi ∧
      ¬Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1764 Fin15AnchoredAtom4515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20880
  ] at hbad
  tauto

theorem fin15Anchored_clause27069 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4515 chi ∧
      Fin15AnchoredAtom1558 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1558 Fin15AnchoredAtom1560 Fin15AnchoredAtom1574
    Fin15AnchoredAtom1589 Fin15AnchoredAtom1764 Fin15AnchoredAtom4515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20880
  ] at hbad
  tauto

theorem fin15Anchored_clause27070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1559 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom4516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24976
  ] at hbad
  tauto

theorem fin15Anchored_clause27071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1560 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1560 Fin15AnchoredAtom4516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24976
  ] at hbad
  tauto

theorem fin15Anchored_clause27072 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom4516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24976
  ] at hbad
  tauto

theorem fin15Anchored_clause27073 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom4516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24976
  ] at hbad
  tauto

theorem fin15Anchored_clause27074 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4516 chi ∧
      ¬Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1765 Fin15AnchoredAtom4516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24976
  ] at hbad
  tauto

theorem fin15Anchored_clause27075 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4516 chi ∧
      Fin15AnchoredAtom1559 chi ∧
      Fin15AnchoredAtom1560 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1559 Fin15AnchoredAtom1560 Fin15AnchoredAtom1575
    Fin15AnchoredAtom1590 Fin15AnchoredAtom1765 Fin15AnchoredAtom4516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24976
  ] at hbad
  tauto

theorem fin15Anchored_clause27076 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom4517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03728
  ] at hbad
  tauto

theorem fin15Anchored_clause27077 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1562 Fin15AnchoredAtom4517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03728
  ] at hbad
  tauto

theorem fin15Anchored_clause27078 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1566 Fin15AnchoredAtom4517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03728
  ] at hbad
  tauto

theorem fin15Anchored_clause27079 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4517 chi ∧
      ¬Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1766 Fin15AnchoredAtom4517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03728
  ] at hbad
  tauto

theorem fin15Anchored_clause27080 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4517 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1562 chi ∧
      Fin15AnchoredAtom1566 chi ∧
      Fin15AnchoredAtom1591 chi ∧
      Fin15AnchoredAtom1766 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom1562 Fin15AnchoredAtom1566
    Fin15AnchoredAtom1591 Fin15AnchoredAtom1766 Fin15AnchoredAtom4517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03728
  ] at hbad
  tauto

theorem fin15Anchored_clause27081 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom4518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05776
  ] at hbad
  tauto

theorem fin15Anchored_clause27082 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom4518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05776
  ] at hbad
  tauto

theorem fin15Anchored_clause27083 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom4518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05776
  ] at hbad
  tauto

theorem fin15Anchored_clause27084 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom4518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05776
  ] at hbad
  tauto

theorem fin15Anchored_clause27085 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4518 chi ∧
      ¬Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1767 Fin15AnchoredAtom4518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05776
  ] at hbad
  tauto

theorem fin15Anchored_clause27086 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4518 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom1563 Fin15AnchoredAtom1567
    Fin15AnchoredAtom1592 Fin15AnchoredAtom1767 Fin15AnchoredAtom4518 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05776
  ] at hbad
  tauto

theorem fin15Anchored_clause27087 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom4519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09872
  ] at hbad
  tauto

theorem fin15Anchored_clause27088 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom4519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09872
  ] at hbad
  tauto

theorem fin15Anchored_clause27089 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom4519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09872
  ] at hbad
  tauto

theorem fin15Anchored_clause27090 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom4519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09872
  ] at hbad
  tauto

theorem fin15Anchored_clause27091 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4519 chi ∧
      ¬Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1768 Fin15AnchoredAtom4519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09872
  ] at hbad
  tauto

theorem fin15Anchored_clause27092 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4519 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1768 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom1564 Fin15AnchoredAtom1568
    Fin15AnchoredAtom1593 Fin15AnchoredAtom1768 Fin15AnchoredAtom4519 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09872
  ] at hbad
  tauto

theorem fin15Anchored_clause27093 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1561 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom4520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18064
  ] at hbad
  tauto

theorem fin15Anchored_clause27094 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom4520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18064
  ] at hbad
  tauto

theorem fin15Anchored_clause27095 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1569 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1569 Fin15AnchoredAtom4520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18064
  ] at hbad
  tauto

theorem fin15Anchored_clause27096 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom4520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18064
  ] at hbad
  tauto

theorem fin15Anchored_clause27097 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4520 chi ∧
      ¬Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1769 Fin15AnchoredAtom4520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18064
  ] at hbad
  tauto

theorem fin15Anchored_clause27098 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4520 chi ∧
      Fin15AnchoredAtom1561 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1569 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1769 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1561 Fin15AnchoredAtom1565 Fin15AnchoredAtom1569
    Fin15AnchoredAtom1594 Fin15AnchoredAtom1769 Fin15AnchoredAtom4520 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18064
  ] at hbad
  tauto

theorem fin15Anchored_clause27099 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom4521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06800
  ] at hbad
  tauto

theorem fin15Anchored_clause27100 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom1595 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1595 Fin15AnchoredAtom4521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06800
  ] at hbad
  tauto

theorem fin15Anchored_clause27101 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4521 chi ∧
      ¬Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1770 Fin15AnchoredAtom4521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06800
  ] at hbad
  tauto

theorem fin15Anchored_clause27102 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4521 chi ∧
      Fin15AnchoredAtom1562 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1595 chi ∧
      Fin15AnchoredAtom1770 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1562 Fin15AnchoredAtom1563 Fin15AnchoredAtom1570
    Fin15AnchoredAtom1595 Fin15AnchoredAtom1770 Fin15AnchoredAtom4521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06800
  ] at hbad
  tauto

theorem fin15Anchored_clause27103 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom4522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10896
  ] at hbad
  tauto

theorem fin15Anchored_clause27104 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1596 Fin15AnchoredAtom4522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10896
  ] at hbad
  tauto

theorem fin15Anchored_clause27105 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4522 chi ∧
      ¬Fin15AnchoredAtom1771 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1771 Fin15AnchoredAtom4522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10896
  ] at hbad
  tauto

theorem fin15Anchored_clause27106 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4523 chi ∧
      ¬Fin15AnchoredAtom1562 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1562 Fin15AnchoredAtom4523 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19088
  ] at hbad
  tauto

theorem fin15Anchored_clause27107 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4523 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom4523 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19088
  ] at hbad
  tauto

theorem fin15Anchored_clause27108 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom4524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12944
  ] at hbad
  tauto

theorem fin15Anchored_clause27109 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom4524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12944
  ] at hbad
  tauto

theorem fin15Anchored_clause27110 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1573 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1573 Fin15AnchoredAtom4524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12944
  ] at hbad
  tauto

theorem fin15Anchored_clause27111 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom4524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12944
  ] at hbad
  tauto

theorem fin15Anchored_clause27112 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4524 chi ∧
      ¬Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1773 Fin15AnchoredAtom4524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12944
  ] at hbad
  tauto

theorem fin15Anchored_clause27113 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4524 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1573 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1773 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom1564 Fin15AnchoredAtom1573
    Fin15AnchoredAtom1598 Fin15AnchoredAtom1773 Fin15AnchoredAtom4524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12944
  ] at hbad
  tauto

theorem fin15Anchored_clause27114 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1563 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom4525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21136
  ] at hbad
  tauto

theorem fin15Anchored_clause27115 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom4525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21136
  ] at hbad
  tauto

theorem fin15Anchored_clause27116 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1574 Fin15AnchoredAtom4525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21136
  ] at hbad
  tauto

theorem fin15Anchored_clause27117 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom4525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21136
  ] at hbad
  tauto

theorem fin15Anchored_clause27118 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4525 chi ∧
      ¬Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1774 Fin15AnchoredAtom4525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21136
  ] at hbad
  tauto

theorem fin15Anchored_clause27119 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4525 chi ∧
      Fin15AnchoredAtom1563 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1574 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1774 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1563 Fin15AnchoredAtom1565 Fin15AnchoredAtom1574
    Fin15AnchoredAtom1599 Fin15AnchoredAtom1774 Fin15AnchoredAtom4525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21136
  ] at hbad
  tauto

theorem fin15Anchored_clause27120 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1564 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom4526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25232
  ] at hbad
  tauto

theorem fin15Anchored_clause27121 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1565 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1565 Fin15AnchoredAtom4526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25232
  ] at hbad
  tauto

theorem fin15Anchored_clause27122 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1575 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1575 Fin15AnchoredAtom4526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25232
  ] at hbad
  tauto

theorem fin15Anchored_clause27123 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom4526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25232
  ] at hbad
  tauto

theorem fin15Anchored_clause27124 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4526 chi ∧
      ¬Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1775 Fin15AnchoredAtom4526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25232
  ] at hbad
  tauto

theorem fin15Anchored_clause27125 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4526 chi ∧
      Fin15AnchoredAtom1564 chi ∧
      Fin15AnchoredAtom1565 chi ∧
      Fin15AnchoredAtom1575 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1564 Fin15AnchoredAtom1565 Fin15AnchoredAtom1575
    Fin15AnchoredAtom1600 Fin15AnchoredAtom1775 Fin15AnchoredAtom4526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25232
  ] at hbad
  tauto

theorem fin15Anchored_clause27126 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom1567 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1567 Fin15AnchoredAtom4527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07312
  ] at hbad
  tauto

theorem fin15Anchored_clause27127 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom1601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1601 Fin15AnchoredAtom4527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07312
  ] at hbad
  tauto

theorem fin15Anchored_clause27128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4527 chi ∧
      ¬Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1776 Fin15AnchoredAtom4527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07312
  ] at hbad
  tauto

theorem fin15Anchored_clause27129 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4527 chi ∧
      Fin15AnchoredAtom1566 chi ∧
      Fin15AnchoredAtom1567 chi ∧
      Fin15AnchoredAtom1570 chi ∧
      Fin15AnchoredAtom1601 chi ∧
      Fin15AnchoredAtom1776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1566 Fin15AnchoredAtom1567 Fin15AnchoredAtom1570
    Fin15AnchoredAtom1601 Fin15AnchoredAtom1776 Fin15AnchoredAtom4527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07312
  ] at hbad
  tauto

theorem fin15Anchored_clause27130 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom1568 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1568 Fin15AnchoredAtom4528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11408
  ] at hbad
  tauto

theorem fin15Anchored_clause27131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4528 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1602 Fin15AnchoredAtom4528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11408
  ] at hbad
  tauto

theorem fin15Anchored_clause27132 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4528 chi ∧
      Fin15AnchoredAtom1566 chi ∧
      Fin15AnchoredAtom1568 chi ∧
      Fin15AnchoredAtom1571 chi ∧
      Fin15AnchoredAtom1602 chi ∧
      Fin15AnchoredAtom1777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1566 Fin15AnchoredAtom1568 Fin15AnchoredAtom1571
    Fin15AnchoredAtom1602 Fin15AnchoredAtom1777 Fin15AnchoredAtom4528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11408
  ] at hbad
  tauto

theorem fin15Anchored_clause27133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4529 chi ∧
      ¬Fin15AnchoredAtom1566 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1566 Fin15AnchoredAtom4529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19600
  ] at hbad
  tauto

theorem fin15Anchored_clause27134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4529 chi ∧
      ¬Fin15AnchoredAtom1603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1603 Fin15AnchoredAtom4529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19600
  ] at hbad
  tauto

theorem fin15Anchored_clause27135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4529 chi ∧
      ¬Fin15AnchoredAtom1778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1778 Fin15AnchoredAtom4529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19600
  ] at hbad
  tauto

end ErdosSzekeres

end
