module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 210. -/

theorem fin15Anchored_clause26880 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4469 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1578 chi ∧
      Fin15AnchoredAtom1718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom1537 Fin15AnchoredAtom1542
    Fin15AnchoredAtom1578 Fin15AnchoredAtom1718 Fin15AnchoredAtom4469 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04944
  ] at hbad
  tauto

theorem fin15Anchored_clause26881 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom4470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09040
  ] at hbad
  tauto

theorem fin15Anchored_clause26882 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1538 Fin15AnchoredAtom4470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09040
  ] at hbad
  tauto

theorem fin15Anchored_clause26883 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom4470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09040
  ] at hbad
  tauto

theorem fin15Anchored_clause26884 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1579 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1579 Fin15AnchoredAtom4470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09040
  ] at hbad
  tauto

theorem fin15Anchored_clause26885 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4470 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom4470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09040
  ] at hbad
  tauto

theorem fin15Anchored_clause26886 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4470 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1579 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom1538 Fin15AnchoredAtom1543
    Fin15AnchoredAtom1579 Fin15AnchoredAtom1719 Fin15AnchoredAtom4470 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09040
  ] at hbad
  tauto

theorem fin15Anchored_clause26887 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom4471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17232
  ] at hbad
  tauto

theorem fin15Anchored_clause26888 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1539 Fin15AnchoredAtom4471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17232
  ] at hbad
  tauto

theorem fin15Anchored_clause26889 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom4471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17232
  ] at hbad
  tauto

theorem fin15Anchored_clause26890 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1580 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1580 Fin15AnchoredAtom4471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17232
  ] at hbad
  tauto

theorem fin15Anchored_clause26891 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4471 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1720 Fin15AnchoredAtom4471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17232
  ] at hbad
  tauto

theorem fin15Anchored_clause26892 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4471 chi ∧
      Fin15AnchoredAtom1534 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1580 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom1539 Fin15AnchoredAtom1544
    Fin15AnchoredAtom1580 Fin15AnchoredAtom1720 Fin15AnchoredAtom4471 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17232
  ] at hbad
  tauto

theorem fin15Anchored_clause26893 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom4473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05456
  ] at hbad
  tauto

theorem fin15Anchored_clause26894 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom4473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05456
  ] at hbad
  tauto

theorem fin15Anchored_clause26895 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom4473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05456
  ] at hbad
  tauto

theorem fin15Anchored_clause26896 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1582 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1582 Fin15AnchoredAtom4473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05456
  ] at hbad
  tauto

theorem fin15Anchored_clause26897 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4473 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom4473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05456
  ] at hbad
  tauto

theorem fin15Anchored_clause26898 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4473 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1582 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom1537 Fin15AnchoredAtom1546
    Fin15AnchoredAtom1582 Fin15AnchoredAtom1722 Fin15AnchoredAtom4473 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05456
  ] at hbad
  tauto

theorem fin15Anchored_clause26899 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom4474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09552
  ] at hbad
  tauto

theorem fin15Anchored_clause26900 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1538 Fin15AnchoredAtom4474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09552
  ] at hbad
  tauto

theorem fin15Anchored_clause26901 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom4474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09552
  ] at hbad
  tauto

theorem fin15Anchored_clause26902 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1583 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1583 Fin15AnchoredAtom4474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09552
  ] at hbad
  tauto

theorem fin15Anchored_clause26903 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4474 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1723 Fin15AnchoredAtom4474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09552
  ] at hbad
  tauto

theorem fin15Anchored_clause26904 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4474 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1583 chi ∧
      Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom1538 Fin15AnchoredAtom1547
    Fin15AnchoredAtom1583 Fin15AnchoredAtom1723 Fin15AnchoredAtom4474 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09552
  ] at hbad
  tauto

theorem fin15Anchored_clause26905 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom4475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17744
  ] at hbad
  tauto

theorem fin15Anchored_clause26906 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1539 Fin15AnchoredAtom4475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17744
  ] at hbad
  tauto

theorem fin15Anchored_clause26907 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom4475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17744
  ] at hbad
  tauto

theorem fin15Anchored_clause26908 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1584 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1584 Fin15AnchoredAtom4475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17744
  ] at hbad
  tauto

theorem fin15Anchored_clause26909 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4475 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1724 Fin15AnchoredAtom4475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17744
  ] at hbad
  tauto

theorem fin15Anchored_clause26910 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4475 chi ∧
      Fin15AnchoredAtom1535 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1584 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom1539 Fin15AnchoredAtom1548
    Fin15AnchoredAtom1584 Fin15AnchoredAtom1724 Fin15AnchoredAtom4475 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17744
  ] at hbad
  tauto

theorem fin15Anchored_clause26911 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom4479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12624
  ] at hbad
  tauto

theorem fin15Anchored_clause26912 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1538 Fin15AnchoredAtom4479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12624
  ] at hbad
  tauto

theorem fin15Anchored_clause26913 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom4479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12624
  ] at hbad
  tauto

theorem fin15Anchored_clause26914 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1588 Fin15AnchoredAtom4479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12624
  ] at hbad
  tauto

theorem fin15Anchored_clause26915 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4479 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom4479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12624
  ] at hbad
  tauto

theorem fin15Anchored_clause26916 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4479 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1588 chi ∧
      Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom1538 Fin15AnchoredAtom1552
    Fin15AnchoredAtom1588 Fin15AnchoredAtom1728 Fin15AnchoredAtom4479 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12624
  ] at hbad
  tauto

theorem fin15Anchored_clause26917 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom4480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20816
  ] at hbad
  tauto

theorem fin15Anchored_clause26918 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1539 Fin15AnchoredAtom4480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20816
  ] at hbad
  tauto

theorem fin15Anchored_clause26919 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom4480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20816
  ] at hbad
  tauto

theorem fin15Anchored_clause26920 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1589 Fin15AnchoredAtom4480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20816
  ] at hbad
  tauto

theorem fin15Anchored_clause26921 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4480 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1729 Fin15AnchoredAtom4480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20816
  ] at hbad
  tauto

theorem fin15Anchored_clause26922 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4480 chi ∧
      Fin15AnchoredAtom1537 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1589 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom1539 Fin15AnchoredAtom1553
    Fin15AnchoredAtom1589 Fin15AnchoredAtom1729 Fin15AnchoredAtom4480 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20816
  ] at hbad
  tauto

theorem fin15Anchored_clause26923 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1538 Fin15AnchoredAtom4481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24912
  ] at hbad
  tauto

theorem fin15Anchored_clause26924 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1539 Fin15AnchoredAtom4481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24912
  ] at hbad
  tauto

theorem fin15Anchored_clause26925 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom4481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24912
  ] at hbad
  tauto

theorem fin15Anchored_clause26926 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1590 Fin15AnchoredAtom4481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24912
  ] at hbad
  tauto

theorem fin15Anchored_clause26927 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4481 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1730 Fin15AnchoredAtom4481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24912
  ] at hbad
  tauto

theorem fin15Anchored_clause26928 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4481 chi ∧
      Fin15AnchoredAtom1538 chi ∧
      Fin15AnchoredAtom1539 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1590 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1538 Fin15AnchoredAtom1539 Fin15AnchoredAtom1554
    Fin15AnchoredAtom1590 Fin15AnchoredAtom1730 Fin15AnchoredAtom4481 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24912
  ] at hbad
  tauto

theorem fin15Anchored_clause26929 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom4482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03664
  ] at hbad
  tauto

theorem fin15Anchored_clause26930 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1541 Fin15AnchoredAtom4482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03664
  ] at hbad
  tauto

theorem fin15Anchored_clause26931 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1545 Fin15AnchoredAtom4482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03664
  ] at hbad
  tauto

theorem fin15Anchored_clause26932 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1591 Fin15AnchoredAtom4482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03664
  ] at hbad
  tauto

theorem fin15Anchored_clause26933 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4482 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1731 Fin15AnchoredAtom4482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03664
  ] at hbad
  tauto

theorem fin15Anchored_clause26934 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4482 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1541 chi ∧
      Fin15AnchoredAtom1545 chi ∧
      Fin15AnchoredAtom1591 chi ∧
      Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom1541 Fin15AnchoredAtom1545
    Fin15AnchoredAtom1591 Fin15AnchoredAtom1731 Fin15AnchoredAtom4482 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03664
  ] at hbad
  tauto

theorem fin15Anchored_clause26935 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom4483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05712
  ] at hbad
  tauto

theorem fin15Anchored_clause26936 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom4483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05712
  ] at hbad
  tauto

theorem fin15Anchored_clause26937 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom4483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05712
  ] at hbad
  tauto

theorem fin15Anchored_clause26938 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1592 Fin15AnchoredAtom4483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05712
  ] at hbad
  tauto

theorem fin15Anchored_clause26939 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4483 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom4483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05712
  ] at hbad
  tauto

theorem fin15Anchored_clause26940 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4483 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1592 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom1542 Fin15AnchoredAtom1546
    Fin15AnchoredAtom1592 Fin15AnchoredAtom1732 Fin15AnchoredAtom4483 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05712
  ] at hbad
  tauto

theorem fin15Anchored_clause26941 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom4484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09808
  ] at hbad
  tauto

theorem fin15Anchored_clause26942 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom4484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09808
  ] at hbad
  tauto

theorem fin15Anchored_clause26943 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom4484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09808
  ] at hbad
  tauto

theorem fin15Anchored_clause26944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1593 Fin15AnchoredAtom4484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09808
  ] at hbad
  tauto

theorem fin15Anchored_clause26945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4484 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom4484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09808
  ] at hbad
  tauto

theorem fin15Anchored_clause26946 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4484 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1593 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom1543 Fin15AnchoredAtom1547
    Fin15AnchoredAtom1593 Fin15AnchoredAtom1733 Fin15AnchoredAtom4484 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09808
  ] at hbad
  tauto

theorem fin15Anchored_clause26947 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom4485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18000
  ] at hbad
  tauto

theorem fin15Anchored_clause26948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom4485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18000
  ] at hbad
  tauto

theorem fin15Anchored_clause26949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom4485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18000
  ] at hbad
  tauto

theorem fin15Anchored_clause26950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1594 Fin15AnchoredAtom4485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18000
  ] at hbad
  tauto

theorem fin15Anchored_clause26951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4485 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom4485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18000
  ] at hbad
  tauto

theorem fin15Anchored_clause26952 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4485 chi ∧
      Fin15AnchoredAtom1540 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1594 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom1544 Fin15AnchoredAtom1548
    Fin15AnchoredAtom1594 Fin15AnchoredAtom1734 Fin15AnchoredAtom4485 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18000
  ] at hbad
  tauto

theorem fin15Anchored_clause26953 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4486 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom4486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06736
  ] at hbad
  tauto

theorem fin15Anchored_clause26954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4486 chi ∧
      ¬Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1549 Fin15AnchoredAtom4486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06736
  ] at hbad
  tauto

theorem fin15Anchored_clause26955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4486 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom4486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06736
  ] at hbad
  tauto

theorem fin15Anchored_clause26956 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4486 chi ∧
      Fin15AnchoredAtom1541 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1549 chi ∧
      Fin15AnchoredAtom1595 chi ∧
      Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1541 Fin15AnchoredAtom1542 Fin15AnchoredAtom1549
    Fin15AnchoredAtom1595 Fin15AnchoredAtom1735 Fin15AnchoredAtom4486 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06736
  ] at hbad
  tauto

theorem fin15Anchored_clause26957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4487 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom4487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10832
  ] at hbad
  tauto

theorem fin15Anchored_clause26958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4487 chi ∧
      ¬Fin15AnchoredAtom1596 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1596 Fin15AnchoredAtom4487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10832
  ] at hbad
  tauto

theorem fin15Anchored_clause26959 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4487 chi ∧
      ¬Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1736 Fin15AnchoredAtom4487 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10832
  ] at hbad
  tauto

theorem fin15Anchored_clause26960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4488 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom4488 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19024
  ] at hbad
  tauto

theorem fin15Anchored_clause26961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom4489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12880
  ] at hbad
  tauto

theorem fin15Anchored_clause26962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom4489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12880
  ] at hbad
  tauto

theorem fin15Anchored_clause26963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom4489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12880
  ] at hbad
  tauto

theorem fin15Anchored_clause26964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1598 Fin15AnchoredAtom4489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12880
  ] at hbad
  tauto

theorem fin15Anchored_clause26965 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4489 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom4489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12880
  ] at hbad
  tauto

theorem fin15Anchored_clause26966 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4489 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1598 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom1543 Fin15AnchoredAtom1552
    Fin15AnchoredAtom1598 Fin15AnchoredAtom1738 Fin15AnchoredAtom4489 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12880
  ] at hbad
  tauto

theorem fin15Anchored_clause26967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom4490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21072
  ] at hbad
  tauto

theorem fin15Anchored_clause26968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom4490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21072
  ] at hbad
  tauto

theorem fin15Anchored_clause26969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom4490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21072
  ] at hbad
  tauto

theorem fin15Anchored_clause26970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1599 Fin15AnchoredAtom4490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21072
  ] at hbad
  tauto

theorem fin15Anchored_clause26971 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4490 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom4490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21072
  ] at hbad
  tauto

theorem fin15Anchored_clause26972 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4490 chi ∧
      Fin15AnchoredAtom1542 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1599 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom1544 Fin15AnchoredAtom1553
    Fin15AnchoredAtom1599 Fin15AnchoredAtom1739 Fin15AnchoredAtom4490 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21072
  ] at hbad
  tauto

theorem fin15Anchored_clause26973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom4491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25168
  ] at hbad
  tauto

theorem fin15Anchored_clause26974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom4491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25168
  ] at hbad
  tauto

theorem fin15Anchored_clause26975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom4491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25168
  ] at hbad
  tauto

theorem fin15Anchored_clause26976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1600 Fin15AnchoredAtom4491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25168
  ] at hbad
  tauto

theorem fin15Anchored_clause26977 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4491 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom4491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25168
  ] at hbad
  tauto

theorem fin15Anchored_clause26978 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4491 chi ∧
      Fin15AnchoredAtom1543 chi ∧
      Fin15AnchoredAtom1544 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1600 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom1544 Fin15AnchoredAtom1554
    Fin15AnchoredAtom1600 Fin15AnchoredAtom1740 Fin15AnchoredAtom4491 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25168
  ] at hbad
  tauto

theorem fin15Anchored_clause26979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom4492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07248
  ] at hbad
  tauto

theorem fin15Anchored_clause26980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1549 Fin15AnchoredAtom4492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07248
  ] at hbad
  tauto

theorem fin15Anchored_clause26981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4492 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1741 Fin15AnchoredAtom4492 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07248
  ] at hbad
  tauto

theorem fin15Anchored_clause26982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4493 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom4493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11344
  ] at hbad
  tauto

theorem fin15Anchored_clause26983 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4493 chi ∧
      ¬Fin15AnchoredAtom1602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1602 Fin15AnchoredAtom4493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11344
  ] at hbad
  tauto

theorem fin15Anchored_clause26984 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4493 chi ∧
      Fin15AnchoredAtom1545 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1550 chi ∧
      Fin15AnchoredAtom1602 chi ∧
      Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1545 Fin15AnchoredAtom1547 Fin15AnchoredAtom1550
    Fin15AnchoredAtom1602 Fin15AnchoredAtom1742 Fin15AnchoredAtom4493 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11344
  ] at hbad
  tauto

theorem fin15Anchored_clause26985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4494 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom4494 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19536
  ] at hbad
  tauto

theorem fin15Anchored_clause26986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4494 chi ∧
      ¬Fin15AnchoredAtom1551 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1551 Fin15AnchoredAtom4494 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19536
  ] at hbad
  tauto

theorem fin15Anchored_clause26987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom4495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13392
  ] at hbad
  tauto

theorem fin15Anchored_clause26988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom4495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13392
  ] at hbad
  tauto

theorem fin15Anchored_clause26989 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom4495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13392
  ] at hbad
  tauto

theorem fin15Anchored_clause26990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1604 Fin15AnchoredAtom4495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13392
  ] at hbad
  tauto

theorem fin15Anchored_clause26991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4495 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom4495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13392
  ] at hbad
  tauto

theorem fin15Anchored_clause26992 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4495 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1604 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom1547 Fin15AnchoredAtom1552
    Fin15AnchoredAtom1604 Fin15AnchoredAtom1744 Fin15AnchoredAtom4495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13392
  ] at hbad
  tauto

theorem fin15Anchored_clause26993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom4496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21584
  ] at hbad
  tauto

theorem fin15Anchored_clause26994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom4496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21584
  ] at hbad
  tauto

theorem fin15Anchored_clause26995 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom4496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21584
  ] at hbad
  tauto

theorem fin15Anchored_clause26996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1605 Fin15AnchoredAtom4496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21584
  ] at hbad
  tauto

theorem fin15Anchored_clause26997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4496 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom4496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21584
  ] at hbad
  tauto

theorem fin15Anchored_clause26998 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4496 chi ∧
      Fin15AnchoredAtom1546 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1553 chi ∧
      Fin15AnchoredAtom1605 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom1548 Fin15AnchoredAtom1553
    Fin15AnchoredAtom1605 Fin15AnchoredAtom1745 Fin15AnchoredAtom4496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21584
  ] at hbad
  tauto

theorem fin15Anchored_clause26999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom4497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25680
  ] at hbad
  tauto

theorem fin15Anchored_clause27000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom4497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25680
  ] at hbad
  tauto

theorem fin15Anchored_clause27001 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom4497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25680
  ] at hbad
  tauto

theorem fin15Anchored_clause27002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1606 Fin15AnchoredAtom4497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25680
  ] at hbad
  tauto

theorem fin15Anchored_clause27003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4497 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom4497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25680
  ] at hbad
  tauto

theorem fin15Anchored_clause27004 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4497 chi ∧
      Fin15AnchoredAtom1547 chi ∧
      Fin15AnchoredAtom1548 chi ∧
      Fin15AnchoredAtom1554 chi ∧
      Fin15AnchoredAtom1606 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom1548 Fin15AnchoredAtom1554
    Fin15AnchoredAtom1606 Fin15AnchoredAtom1746 Fin15AnchoredAtom4497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25680
  ] at hbad
  tauto

theorem fin15Anchored_clause27005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4498 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom4498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14416
  ] at hbad
  tauto

theorem fin15Anchored_clause27006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4498 chi ∧
      ¬Fin15AnchoredAtom1607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1607 Fin15AnchoredAtom4498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14416
  ] at hbad
  tauto

theorem fin15Anchored_clause27007 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4498 chi ∧
      Fin15AnchoredAtom1549 chi ∧
      Fin15AnchoredAtom1550 chi ∧
      Fin15AnchoredAtom1552 chi ∧
      Fin15AnchoredAtom1607 chi ∧
      Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1549 Fin15AnchoredAtom1550 Fin15AnchoredAtom1552
    Fin15AnchoredAtom1607 Fin15AnchoredAtom1747 Fin15AnchoredAtom4498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14416
  ] at hbad
  tauto

end ErdosSzekeres

end
