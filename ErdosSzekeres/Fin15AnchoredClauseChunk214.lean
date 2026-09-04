module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 214. -/

theorem fin15Anchored_clause27392 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom4596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09056
  ] at hbad
  tauto

theorem fin15Anchored_clause27393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom4596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09056
  ] at hbad
  tauto

theorem fin15Anchored_clause27394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom4596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09056
  ] at hbad
  tauto

theorem fin15Anchored_clause27395 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4596 chi ∧
      ¬Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1719 Fin15AnchoredAtom4596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09056
  ] at hbad
  tauto

theorem fin15Anchored_clause27396 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4596 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1663 chi ∧
      Fin15AnchoredAtom1719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom1622 Fin15AnchoredAtom1627
    Fin15AnchoredAtom1663 Fin15AnchoredAtom1719 Fin15AnchoredAtom4596 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09056
  ] at hbad
  tauto

theorem fin15Anchored_clause27397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom4597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17248
  ] at hbad
  tauto

theorem fin15Anchored_clause27398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1623 Fin15AnchoredAtom4597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17248
  ] at hbad
  tauto

theorem fin15Anchored_clause27399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom4597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17248
  ] at hbad
  tauto

theorem fin15Anchored_clause27400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1664 Fin15AnchoredAtom4597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17248
  ] at hbad
  tauto

theorem fin15Anchored_clause27401 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4597 chi ∧
      ¬Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1720 Fin15AnchoredAtom4597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17248
  ] at hbad
  tauto

theorem fin15Anchored_clause27402 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4597 chi ∧
      Fin15AnchoredAtom1618 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1664 chi ∧
      Fin15AnchoredAtom1720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1618 Fin15AnchoredAtom1623 Fin15AnchoredAtom1628
    Fin15AnchoredAtom1664 Fin15AnchoredAtom1720 Fin15AnchoredAtom4597 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17248
  ] at hbad
  tauto

theorem fin15Anchored_clause27403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom4599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05472
  ] at hbad
  tauto

theorem fin15Anchored_clause27404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom4599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05472
  ] at hbad
  tauto

theorem fin15Anchored_clause27405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom4599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05472
  ] at hbad
  tauto

theorem fin15Anchored_clause27406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom4599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05472
  ] at hbad
  tauto

theorem fin15Anchored_clause27407 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4599 chi ∧
      ¬Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1722 Fin15AnchoredAtom4599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05472
  ] at hbad
  tauto

theorem fin15Anchored_clause27408 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4599 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1666 chi ∧
      Fin15AnchoredAtom1722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom1621 Fin15AnchoredAtom1630
    Fin15AnchoredAtom1666 Fin15AnchoredAtom1722 Fin15AnchoredAtom4599 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05472
  ] at hbad
  tauto

theorem fin15Anchored_clause27409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom4600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09568
  ] at hbad
  tauto

theorem fin15Anchored_clause27410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom4600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09568
  ] at hbad
  tauto

theorem fin15Anchored_clause27411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom4600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09568
  ] at hbad
  tauto

theorem fin15Anchored_clause27412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom4600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09568
  ] at hbad
  tauto

theorem fin15Anchored_clause27413 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4600 chi ∧
      ¬Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1723 Fin15AnchoredAtom4600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09568
  ] at hbad
  tauto

theorem fin15Anchored_clause27414 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4600 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1667 chi ∧
      Fin15AnchoredAtom1723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom1622 Fin15AnchoredAtom1631
    Fin15AnchoredAtom1667 Fin15AnchoredAtom1723 Fin15AnchoredAtom4600 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09568
  ] at hbad
  tauto

theorem fin15Anchored_clause27415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom4601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17760
  ] at hbad
  tauto

theorem fin15Anchored_clause27416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1623 Fin15AnchoredAtom4601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17760
  ] at hbad
  tauto

theorem fin15Anchored_clause27417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom4601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17760
  ] at hbad
  tauto

theorem fin15Anchored_clause27418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1668 Fin15AnchoredAtom4601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17760
  ] at hbad
  tauto

theorem fin15Anchored_clause27419 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4601 chi ∧
      ¬Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1724 Fin15AnchoredAtom4601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17760
  ] at hbad
  tauto

theorem fin15Anchored_clause27420 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4601 chi ∧
      Fin15AnchoredAtom1619 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1668 chi ∧
      Fin15AnchoredAtom1724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1619 Fin15AnchoredAtom1623 Fin15AnchoredAtom1632
    Fin15AnchoredAtom1668 Fin15AnchoredAtom1724 Fin15AnchoredAtom4601 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17760
  ] at hbad
  tauto

theorem fin15Anchored_clause27421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom4605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12640
  ] at hbad
  tauto

theorem fin15Anchored_clause27422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom4605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12640
  ] at hbad
  tauto

theorem fin15Anchored_clause27423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom4605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12640
  ] at hbad
  tauto

theorem fin15Anchored_clause27424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom4605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12640
  ] at hbad
  tauto

theorem fin15Anchored_clause27425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4605 chi ∧
      ¬Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1728 Fin15AnchoredAtom4605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12640
  ] at hbad
  tauto

theorem fin15Anchored_clause27426 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4605 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1672 chi ∧
      Fin15AnchoredAtom1728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom1622 Fin15AnchoredAtom1636
    Fin15AnchoredAtom1672 Fin15AnchoredAtom1728 Fin15AnchoredAtom4605 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12640
  ] at hbad
  tauto

theorem fin15Anchored_clause27427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom4606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20832
  ] at hbad
  tauto

theorem fin15Anchored_clause27428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1623 Fin15AnchoredAtom4606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20832
  ] at hbad
  tauto

theorem fin15Anchored_clause27429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom4606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20832
  ] at hbad
  tauto

theorem fin15Anchored_clause27430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1673 Fin15AnchoredAtom4606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20832
  ] at hbad
  tauto

theorem fin15Anchored_clause27431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4606 chi ∧
      ¬Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1729 Fin15AnchoredAtom4606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20832
  ] at hbad
  tauto

theorem fin15Anchored_clause27432 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4606 chi ∧
      Fin15AnchoredAtom1621 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1673 chi ∧
      Fin15AnchoredAtom1729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1621 Fin15AnchoredAtom1623 Fin15AnchoredAtom1637
    Fin15AnchoredAtom1673 Fin15AnchoredAtom1729 Fin15AnchoredAtom4606 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20832
  ] at hbad
  tauto

theorem fin15Anchored_clause27433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom1622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom4607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24928
  ] at hbad
  tauto

theorem fin15Anchored_clause27434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom4607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24928
  ] at hbad
  tauto

theorem fin15Anchored_clause27435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1674 Fin15AnchoredAtom4607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24928
  ] at hbad
  tauto

theorem fin15Anchored_clause27436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4607 chi ∧
      ¬Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1730 Fin15AnchoredAtom4607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24928
  ] at hbad
  tauto

theorem fin15Anchored_clause27437 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4607 chi ∧
      Fin15AnchoredAtom1622 chi ∧
      Fin15AnchoredAtom1623 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1674 chi ∧
      Fin15AnchoredAtom1730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1622 Fin15AnchoredAtom1623 Fin15AnchoredAtom1638
    Fin15AnchoredAtom1674 Fin15AnchoredAtom1730 Fin15AnchoredAtom4607 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24928
  ] at hbad
  tauto

theorem fin15Anchored_clause27438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4608 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom4608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03680
  ] at hbad
  tauto

theorem fin15Anchored_clause27439 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4608 chi ∧
      ¬Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1731 Fin15AnchoredAtom4608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03680
  ] at hbad
  tauto

theorem fin15Anchored_clause27440 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4608 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1625 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1675 chi ∧
      Fin15AnchoredAtom1731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom1625 Fin15AnchoredAtom1629
    Fin15AnchoredAtom1675 Fin15AnchoredAtom1731 Fin15AnchoredAtom4608 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03680
  ] at hbad
  tauto

theorem fin15Anchored_clause27441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom4609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05728
  ] at hbad
  tauto

theorem fin15Anchored_clause27442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom4609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05728
  ] at hbad
  tauto

theorem fin15Anchored_clause27443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom4609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05728
  ] at hbad
  tauto

theorem fin15Anchored_clause27444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom4609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05728
  ] at hbad
  tauto

theorem fin15Anchored_clause27445 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4609 chi ∧
      ¬Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1732 Fin15AnchoredAtom4609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05728
  ] at hbad
  tauto

theorem fin15Anchored_clause27446 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4609 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1676 chi ∧
      Fin15AnchoredAtom1732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom1626 Fin15AnchoredAtom1630
    Fin15AnchoredAtom1676 Fin15AnchoredAtom1732 Fin15AnchoredAtom4609 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05728
  ] at hbad
  tauto

theorem fin15Anchored_clause27447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom4610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09824
  ] at hbad
  tauto

theorem fin15Anchored_clause27448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom4610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09824
  ] at hbad
  tauto

theorem fin15Anchored_clause27449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom4610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09824
  ] at hbad
  tauto

theorem fin15Anchored_clause27450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom4610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09824
  ] at hbad
  tauto

theorem fin15Anchored_clause27451 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4610 chi ∧
      ¬Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1733 Fin15AnchoredAtom4610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09824
  ] at hbad
  tauto

theorem fin15Anchored_clause27452 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4610 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1677 chi ∧
      Fin15AnchoredAtom1733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom1627 Fin15AnchoredAtom1631
    Fin15AnchoredAtom1677 Fin15AnchoredAtom1733 Fin15AnchoredAtom4610 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09824
  ] at hbad
  tauto

theorem fin15Anchored_clause27453 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom4611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18016
  ] at hbad
  tauto

theorem fin15Anchored_clause27454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom4611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18016
  ] at hbad
  tauto

theorem fin15Anchored_clause27455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom4611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18016
  ] at hbad
  tauto

theorem fin15Anchored_clause27456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom4611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18016
  ] at hbad
  tauto

theorem fin15Anchored_clause27457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4611 chi ∧
      ¬Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1734 Fin15AnchoredAtom4611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18016
  ] at hbad
  tauto

theorem fin15Anchored_clause27458 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4611 chi ∧
      Fin15AnchoredAtom1624 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1678 chi ∧
      Fin15AnchoredAtom1734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1624 Fin15AnchoredAtom1628 Fin15AnchoredAtom1632
    Fin15AnchoredAtom1678 Fin15AnchoredAtom1734 Fin15AnchoredAtom4611 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18016
  ] at hbad
  tauto

theorem fin15Anchored_clause27459 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4612 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom4612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06752
  ] at hbad
  tauto

theorem fin15Anchored_clause27460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4612 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1679 Fin15AnchoredAtom4612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06752
  ] at hbad
  tauto

theorem fin15Anchored_clause27461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4612 chi ∧
      ¬Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1735 Fin15AnchoredAtom4612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06752
  ] at hbad
  tauto

theorem fin15Anchored_clause27462 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4612 chi ∧
      Fin15AnchoredAtom1625 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1633 chi ∧
      Fin15AnchoredAtom1679 chi ∧
      Fin15AnchoredAtom1735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1625 Fin15AnchoredAtom1626 Fin15AnchoredAtom1633
    Fin15AnchoredAtom1679 Fin15AnchoredAtom1735 Fin15AnchoredAtom4612 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06752
  ] at hbad
  tauto

theorem fin15Anchored_clause27463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom4613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10848
  ] at hbad
  tauto

theorem fin15Anchored_clause27464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1680 Fin15AnchoredAtom4613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10848
  ] at hbad
  tauto

theorem fin15Anchored_clause27465 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4613 chi ∧
      ¬Fin15AnchoredAtom1736 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1736 Fin15AnchoredAtom4613 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10848
  ] at hbad
  tauto

theorem fin15Anchored_clause27466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4614 chi ∧
      ¬Fin15AnchoredAtom1737 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1737 Fin15AnchoredAtom4614 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19040
  ] at hbad
  tauto

theorem fin15Anchored_clause27467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom4615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12896
  ] at hbad
  tauto

theorem fin15Anchored_clause27468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom4615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12896
  ] at hbad
  tauto

theorem fin15Anchored_clause27469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom4615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12896
  ] at hbad
  tauto

theorem fin15Anchored_clause27470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom4615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12896
  ] at hbad
  tauto

theorem fin15Anchored_clause27471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4615 chi ∧
      ¬Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1738 Fin15AnchoredAtom4615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12896
  ] at hbad
  tauto

theorem fin15Anchored_clause27472 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4615 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1682 chi ∧
      Fin15AnchoredAtom1738 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom1627 Fin15AnchoredAtom1636
    Fin15AnchoredAtom1682 Fin15AnchoredAtom1738 Fin15AnchoredAtom4615 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12896
  ] at hbad
  tauto

theorem fin15Anchored_clause27473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1626 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom4616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21088
  ] at hbad
  tauto

theorem fin15Anchored_clause27474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom4616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21088
  ] at hbad
  tauto

theorem fin15Anchored_clause27475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom4616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21088
  ] at hbad
  tauto

theorem fin15Anchored_clause27476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom4616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21088
  ] at hbad
  tauto

theorem fin15Anchored_clause27477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4616 chi ∧
      ¬Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1739 Fin15AnchoredAtom4616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21088
  ] at hbad
  tauto

theorem fin15Anchored_clause27478 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4616 chi ∧
      Fin15AnchoredAtom1626 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1683 chi ∧
      Fin15AnchoredAtom1739 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1626 Fin15AnchoredAtom1628 Fin15AnchoredAtom1637
    Fin15AnchoredAtom1683 Fin15AnchoredAtom1739 Fin15AnchoredAtom4616 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21088
  ] at hbad
  tauto

theorem fin15Anchored_clause27479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1627 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom4617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25184
  ] at hbad
  tauto

theorem fin15Anchored_clause27480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1628 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1628 Fin15AnchoredAtom4617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25184
  ] at hbad
  tauto

theorem fin15Anchored_clause27481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom4617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25184
  ] at hbad
  tauto

theorem fin15Anchored_clause27482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom4617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25184
  ] at hbad
  tauto

theorem fin15Anchored_clause27483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4617 chi ∧
      ¬Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1740 Fin15AnchoredAtom4617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25184
  ] at hbad
  tauto

theorem fin15Anchored_clause27484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4617 chi ∧
      Fin15AnchoredAtom1627 chi ∧
      Fin15AnchoredAtom1628 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1684 chi ∧
      Fin15AnchoredAtom1740 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1627 Fin15AnchoredAtom1628 Fin15AnchoredAtom1638
    Fin15AnchoredAtom1684 Fin15AnchoredAtom1740 Fin15AnchoredAtom4617 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25184
  ] at hbad
  tauto

theorem fin15Anchored_clause27485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom1629 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1629 Fin15AnchoredAtom4618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07264
  ] at hbad
  tauto

theorem fin15Anchored_clause27486 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom4618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07264
  ] at hbad
  tauto

theorem fin15Anchored_clause27487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1685 Fin15AnchoredAtom4618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07264
  ] at hbad
  tauto

theorem fin15Anchored_clause27488 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4618 chi ∧
      ¬Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1741 Fin15AnchoredAtom4618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07264
  ] at hbad
  tauto

theorem fin15Anchored_clause27489 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4618 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1633 chi ∧
      Fin15AnchoredAtom1685 chi ∧
      Fin15AnchoredAtom1741 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1629 Fin15AnchoredAtom1630 Fin15AnchoredAtom1633
    Fin15AnchoredAtom1685 Fin15AnchoredAtom1741 Fin15AnchoredAtom4618 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07264
  ] at hbad
  tauto

theorem fin15Anchored_clause27490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4619 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom4619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11360
  ] at hbad
  tauto

theorem fin15Anchored_clause27491 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4619 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1634 chi ∧
      Fin15AnchoredAtom1686 chi ∧
      Fin15AnchoredAtom1742 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1629 Fin15AnchoredAtom1631 Fin15AnchoredAtom1634
    Fin15AnchoredAtom1686 Fin15AnchoredAtom1742 Fin15AnchoredAtom4619 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11360
  ] at hbad
  tauto

theorem fin15Anchored_clause27492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4620 chi ∧
      ¬Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1687 Fin15AnchoredAtom4620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19552
  ] at hbad
  tauto

theorem fin15Anchored_clause27493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4620 chi ∧
      ¬Fin15AnchoredAtom1743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1743 Fin15AnchoredAtom4620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19552
  ] at hbad
  tauto

theorem fin15Anchored_clause27494 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4620 chi ∧
      Fin15AnchoredAtom1629 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1635 chi ∧
      Fin15AnchoredAtom1687 chi ∧
      Fin15AnchoredAtom1743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1629 Fin15AnchoredAtom1632 Fin15AnchoredAtom1635
    Fin15AnchoredAtom1687 Fin15AnchoredAtom1743 Fin15AnchoredAtom4620 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19552
  ] at hbad
  tauto

theorem fin15Anchored_clause27495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom4621 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13408
  ] at hbad
  tauto

theorem fin15Anchored_clause27496 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom4621 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13408
  ] at hbad
  tauto

theorem fin15Anchored_clause27497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom4621 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13408
  ] at hbad
  tauto

theorem fin15Anchored_clause27498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1688 Fin15AnchoredAtom4621 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13408
  ] at hbad
  tauto

theorem fin15Anchored_clause27499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4621 chi ∧
      ¬Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1744 Fin15AnchoredAtom4621 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13408
  ] at hbad
  tauto

theorem fin15Anchored_clause27500 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4621 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1688 chi ∧
      Fin15AnchoredAtom1744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom1631 Fin15AnchoredAtom1636
    Fin15AnchoredAtom1688 Fin15AnchoredAtom1744 Fin15AnchoredAtom4621 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13408
  ] at hbad
  tauto

theorem fin15Anchored_clause27501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1630 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom4622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21600
  ] at hbad
  tauto

theorem fin15Anchored_clause27502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom4622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21600
  ] at hbad
  tauto

theorem fin15Anchored_clause27503 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom4622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21600
  ] at hbad
  tauto

theorem fin15Anchored_clause27504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1689 Fin15AnchoredAtom4622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21600
  ] at hbad
  tauto

theorem fin15Anchored_clause27505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4622 chi ∧
      ¬Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1745 Fin15AnchoredAtom4622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21600
  ] at hbad
  tauto

theorem fin15Anchored_clause27506 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4622 chi ∧
      Fin15AnchoredAtom1630 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1637 chi ∧
      Fin15AnchoredAtom1689 chi ∧
      Fin15AnchoredAtom1745 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1630 Fin15AnchoredAtom1632 Fin15AnchoredAtom1637
    Fin15AnchoredAtom1689 Fin15AnchoredAtom1745 Fin15AnchoredAtom4622 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21600
  ] at hbad
  tauto

theorem fin15Anchored_clause27507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1631 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom4623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25696
  ] at hbad
  tauto

theorem fin15Anchored_clause27508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1632 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1632 Fin15AnchoredAtom4623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25696
  ] at hbad
  tauto

theorem fin15Anchored_clause27509 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1638 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1638 Fin15AnchoredAtom4623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25696
  ] at hbad
  tauto

theorem fin15Anchored_clause27510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1690 Fin15AnchoredAtom4623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25696
  ] at hbad
  tauto

theorem fin15Anchored_clause27511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4623 chi ∧
      ¬Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1746 Fin15AnchoredAtom4623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25696
  ] at hbad
  tauto

theorem fin15Anchored_clause27512 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4623 chi ∧
      Fin15AnchoredAtom1631 chi ∧
      Fin15AnchoredAtom1632 chi ∧
      Fin15AnchoredAtom1638 chi ∧
      Fin15AnchoredAtom1690 chi ∧
      Fin15AnchoredAtom1746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1631 Fin15AnchoredAtom1632 Fin15AnchoredAtom1638
    Fin15AnchoredAtom1690 Fin15AnchoredAtom1746 Fin15AnchoredAtom4623 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25696
  ] at hbad
  tauto

theorem fin15Anchored_clause27513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom1634 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1634 Fin15AnchoredAtom4624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14432
  ] at hbad
  tauto

theorem fin15Anchored_clause27514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom4624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14432
  ] at hbad
  tauto

theorem fin15Anchored_clause27515 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4624 chi ∧
      ¬Fin15AnchoredAtom1691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1691 Fin15AnchoredAtom4624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14432
  ] at hbad
  tauto

theorem fin15Anchored_clause27516 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom4624 chi ∧
      Fin15AnchoredAtom1633 chi ∧
      Fin15AnchoredAtom1634 chi ∧
      Fin15AnchoredAtom1636 chi ∧
      Fin15AnchoredAtom1691 chi ∧
      Fin15AnchoredAtom1747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1633 Fin15AnchoredAtom1634 Fin15AnchoredAtom1636
    Fin15AnchoredAtom1691 Fin15AnchoredAtom1747 Fin15AnchoredAtom4624 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14432
  ] at hbad
  tauto

theorem fin15Anchored_clause27517 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4625 chi ∧
      ¬Fin15AnchoredAtom1692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1692 Fin15AnchoredAtom4625 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22624
  ] at hbad
  tauto

theorem fin15Anchored_clause27518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1636 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1636 Fin15AnchoredAtom4627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28768
  ] at hbad
  tauto

theorem fin15Anchored_clause27519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom4627 chi ∧
      ¬Fin15AnchoredAtom1637 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1637 Fin15AnchoredAtom4627 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28768
  ] at hbad
  tauto

end ErdosSzekeres

end
