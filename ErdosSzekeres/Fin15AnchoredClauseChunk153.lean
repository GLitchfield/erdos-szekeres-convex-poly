module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 153. -/

theorem fin15Anchored_clause19584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2661 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01825
  ] at hbad
  tauto

theorem fin15Anchored_clause19585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom2661 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01825
  ] at hbad
  tauto

theorem fin15Anchored_clause19586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2661 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01825
  ] at hbad
  tauto

theorem fin15Anchored_clause19587 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom2661 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01825
  ] at hbad
  tauto

theorem fin15Anchored_clause19588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2661 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom2661 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01825
  ] at hbad
  tauto

theorem fin15Anchored_clause19589 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2661 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom0716 Fin15AnchoredAtom0721
    Fin15AnchoredAtom0785 Fin15AnchoredAtom1660 Fin15AnchoredAtom2661 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01825
  ] at hbad
  tauto

theorem fin15Anchored_clause19590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2663 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04897
  ] at hbad
  tauto

theorem fin15Anchored_clause19591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom2663 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04897
  ] at hbad
  tauto

theorem fin15Anchored_clause19592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2663 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04897
  ] at hbad
  tauto

theorem fin15Anchored_clause19593 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom2663 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04897
  ] at hbad
  tauto

theorem fin15Anchored_clause19594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2663 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom2663 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04897
  ] at hbad
  tauto

theorem fin15Anchored_clause19595 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2663 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom0718 Fin15AnchoredAtom0723
    Fin15AnchoredAtom0787 Fin15AnchoredAtom1662 Fin15AnchoredAtom2663 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04897
  ] at hbad
  tauto

theorem fin15Anchored_clause19596 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08993
  ] at hbad
  tauto

theorem fin15Anchored_clause19597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08993
  ] at hbad
  tauto

theorem fin15Anchored_clause19598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom2664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08993
  ] at hbad
  tauto

theorem fin15Anchored_clause19599 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2664 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom2664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08993
  ] at hbad
  tauto

theorem fin15Anchored_clause19600 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2664 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom0719 Fin15AnchoredAtom0724
    Fin15AnchoredAtom0788 Fin15AnchoredAtom1663 Fin15AnchoredAtom2664 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08993
  ] at hbad
  tauto

theorem fin15Anchored_clause19601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom0715 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom2665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17185
  ] at hbad
  tauto

theorem fin15Anchored_clause19602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0720 Fin15AnchoredAtom2665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17185
  ] at hbad
  tauto

theorem fin15Anchored_clause19603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17185
  ] at hbad
  tauto

theorem fin15Anchored_clause19604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0789 Fin15AnchoredAtom2665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17185
  ] at hbad
  tauto

theorem fin15Anchored_clause19605 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2665 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1664 Fin15AnchoredAtom2665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17185
  ] at hbad
  tauto

theorem fin15Anchored_clause19606 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2665 chi ∧
      Fin15AnchoredAtom0715 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0715 Fin15AnchoredAtom0720 Fin15AnchoredAtom0725
    Fin15AnchoredAtom0789 Fin15AnchoredAtom1664 Fin15AnchoredAtom2665 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17185
  ] at hbad
  tauto

theorem fin15Anchored_clause19607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom2667 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05409
  ] at hbad
  tauto

theorem fin15Anchored_clause19608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom2667 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05409
  ] at hbad
  tauto

theorem fin15Anchored_clause19609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2667 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05409
  ] at hbad
  tauto

theorem fin15Anchored_clause19610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom2667 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05409
  ] at hbad
  tauto

theorem fin15Anchored_clause19611 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2667 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom2667 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05409
  ] at hbad
  tauto

theorem fin15Anchored_clause19612 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2667 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom0718 Fin15AnchoredAtom0727
    Fin15AnchoredAtom0791 Fin15AnchoredAtom1666 Fin15AnchoredAtom2667 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05409
  ] at hbad
  tauto

theorem fin15Anchored_clause19613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom2668 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09505
  ] at hbad
  tauto

theorem fin15Anchored_clause19614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2668 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09505
  ] at hbad
  tauto

theorem fin15Anchored_clause19615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2668 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09505
  ] at hbad
  tauto

theorem fin15Anchored_clause19616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2668 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom2668 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09505
  ] at hbad
  tauto

theorem fin15Anchored_clause19617 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2668 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom0719 Fin15AnchoredAtom0728
    Fin15AnchoredAtom0792 Fin15AnchoredAtom1667 Fin15AnchoredAtom2668 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09505
  ] at hbad
  tauto

theorem fin15Anchored_clause19618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom0716 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom2669 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17697
  ] at hbad
  tauto

theorem fin15Anchored_clause19619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0720 Fin15AnchoredAtom2669 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17697
  ] at hbad
  tauto

theorem fin15Anchored_clause19620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2669 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17697
  ] at hbad
  tauto

theorem fin15Anchored_clause19621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0793 Fin15AnchoredAtom2669 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17697
  ] at hbad
  tauto

theorem fin15Anchored_clause19622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2669 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1668 Fin15AnchoredAtom2669 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17697
  ] at hbad
  tauto

theorem fin15Anchored_clause19623 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2669 chi ∧
      Fin15AnchoredAtom0716 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0716 Fin15AnchoredAtom0720 Fin15AnchoredAtom0729
    Fin15AnchoredAtom0793 Fin15AnchoredAtom1668 Fin15AnchoredAtom2669 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17697
  ] at hbad
  tauto

theorem fin15Anchored_clause19624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom2673 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12577
  ] at hbad
  tauto

theorem fin15Anchored_clause19625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom0719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0719 Fin15AnchoredAtom2673 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12577
  ] at hbad
  tauto

theorem fin15Anchored_clause19626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2673 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12577
  ] at hbad
  tauto

theorem fin15Anchored_clause19627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2673 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2673 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12577
  ] at hbad
  tauto

theorem fin15Anchored_clause19628 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2673 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom0719 Fin15AnchoredAtom0733
    Fin15AnchoredAtom0797 Fin15AnchoredAtom1672 Fin15AnchoredAtom2673 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12577
  ] at hbad
  tauto

theorem fin15Anchored_clause19629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom0718 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom2674 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20769
  ] at hbad
  tauto

theorem fin15Anchored_clause19630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0720 Fin15AnchoredAtom2674 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20769
  ] at hbad
  tauto

theorem fin15Anchored_clause19631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2674 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20769
  ] at hbad
  tauto

theorem fin15Anchored_clause19632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0798 Fin15AnchoredAtom2674 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20769
  ] at hbad
  tauto

theorem fin15Anchored_clause19633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2674 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1673 Fin15AnchoredAtom2674 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20769
  ] at hbad
  tauto

theorem fin15Anchored_clause19634 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2674 chi ∧
      Fin15AnchoredAtom0718 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0718 Fin15AnchoredAtom0720 Fin15AnchoredAtom0734
    Fin15AnchoredAtom0798 Fin15AnchoredAtom1673 Fin15AnchoredAtom2674 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20769
  ] at hbad
  tauto

theorem fin15Anchored_clause19635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom0719 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0719 Fin15AnchoredAtom2675 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24865
  ] at hbad
  tauto

theorem fin15Anchored_clause19636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom0720 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0720 Fin15AnchoredAtom2675 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24865
  ] at hbad
  tauto

theorem fin15Anchored_clause19637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2675 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24865
  ] at hbad
  tauto

theorem fin15Anchored_clause19638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0799 Fin15AnchoredAtom2675 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24865
  ] at hbad
  tauto

theorem fin15Anchored_clause19639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2675 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1674 Fin15AnchoredAtom2675 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24865
  ] at hbad
  tauto

theorem fin15Anchored_clause19640 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2675 chi ∧
      Fin15AnchoredAtom0719 chi ∧
      Fin15AnchoredAtom0720 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0719 Fin15AnchoredAtom0720 Fin15AnchoredAtom0735
    Fin15AnchoredAtom0799 Fin15AnchoredAtom1674 Fin15AnchoredAtom2675 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24865
  ] at hbad
  tauto

theorem fin15Anchored_clause19641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2676 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2676 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03617
  ] at hbad
  tauto

theorem fin15Anchored_clause19642 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2676 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0800 chi ∧
      Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom0722 Fin15AnchoredAtom0726
    Fin15AnchoredAtom0800 Fin15AnchoredAtom1675 Fin15AnchoredAtom2676 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03617
  ] at hbad
  tauto

theorem fin15Anchored_clause19643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05665
  ] at hbad
  tauto

theorem fin15Anchored_clause19644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05665
  ] at hbad
  tauto

theorem fin15Anchored_clause19645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05665
  ] at hbad
  tauto

theorem fin15Anchored_clause19646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05665
  ] at hbad
  tauto

theorem fin15Anchored_clause19647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2677 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom2677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05665
  ] at hbad
  tauto

theorem fin15Anchored_clause19648 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2677 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom0723 Fin15AnchoredAtom0727
    Fin15AnchoredAtom0801 Fin15AnchoredAtom1676 Fin15AnchoredAtom2677 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05665
  ] at hbad
  tauto

theorem fin15Anchored_clause19649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09761
  ] at hbad
  tauto

theorem fin15Anchored_clause19650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09761
  ] at hbad
  tauto

theorem fin15Anchored_clause19651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09761
  ] at hbad
  tauto

theorem fin15Anchored_clause19652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09761
  ] at hbad
  tauto

theorem fin15Anchored_clause19653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2678 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom2678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09761
  ] at hbad
  tauto

theorem fin15Anchored_clause19654 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2678 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom0724 Fin15AnchoredAtom0728
    Fin15AnchoredAtom0802 Fin15AnchoredAtom1677 Fin15AnchoredAtom2678 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09761
  ] at hbad
  tauto

theorem fin15Anchored_clause19655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom0721 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom2679 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17953
  ] at hbad
  tauto

theorem fin15Anchored_clause19656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2679 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17953
  ] at hbad
  tauto

theorem fin15Anchored_clause19657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2679 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17953
  ] at hbad
  tauto

theorem fin15Anchored_clause19658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2679 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17953
  ] at hbad
  tauto

theorem fin15Anchored_clause19659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2679 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom2679 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17953
  ] at hbad
  tauto

theorem fin15Anchored_clause19660 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2679 chi ∧
      Fin15AnchoredAtom0721 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0721 Fin15AnchoredAtom0725 Fin15AnchoredAtom0729
    Fin15AnchoredAtom0803 Fin15AnchoredAtom1678 Fin15AnchoredAtom2679 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17953
  ] at hbad
  tauto

theorem fin15Anchored_clause19661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom0722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0722 Fin15AnchoredAtom2680 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06689
  ] at hbad
  tauto

theorem fin15Anchored_clause19662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2680 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06689
  ] at hbad
  tauto

theorem fin15Anchored_clause19663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom2680 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06689
  ] at hbad
  tauto

theorem fin15Anchored_clause19664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom2680 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06689
  ] at hbad
  tauto

theorem fin15Anchored_clause19665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2680 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1679 Fin15AnchoredAtom2680 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06689
  ] at hbad
  tauto

theorem fin15Anchored_clause19666 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2680 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0804 chi ∧
      Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0722 Fin15AnchoredAtom0723 Fin15AnchoredAtom0730
    Fin15AnchoredAtom0804 Fin15AnchoredAtom1679 Fin15AnchoredAtom2680 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06689
  ] at hbad
  tauto

theorem fin15Anchored_clause19667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2681 chi ∧
      ¬Fin15AnchoredAtom0722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0722 Fin15AnchoredAtom2681 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10785
  ] at hbad
  tauto

theorem fin15Anchored_clause19668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2681 chi ∧
      ¬Fin15AnchoredAtom0805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0805 Fin15AnchoredAtom2681 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10785
  ] at hbad
  tauto

theorem fin15Anchored_clause19669 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2681 chi ∧
      Fin15AnchoredAtom0722 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0805 chi ∧
      Fin15AnchoredAtom1680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0722 Fin15AnchoredAtom0724 Fin15AnchoredAtom0731
    Fin15AnchoredAtom0805 Fin15AnchoredAtom1680 Fin15AnchoredAtom2681 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10785
  ] at hbad
  tauto

theorem fin15Anchored_clause19670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom0722 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0722 Fin15AnchoredAtom2682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18977
  ] at hbad
  tauto

theorem fin15Anchored_clause19671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom0732 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0732 Fin15AnchoredAtom2682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18977
  ] at hbad
  tauto

theorem fin15Anchored_clause19672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom0806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0806 Fin15AnchoredAtom2682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18977
  ] at hbad
  tauto

theorem fin15Anchored_clause19673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2682 chi ∧
      ¬Fin15AnchoredAtom1681 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1681 Fin15AnchoredAtom2682 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18977
  ] at hbad
  tauto

theorem fin15Anchored_clause19674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12833
  ] at hbad
  tauto

theorem fin15Anchored_clause19675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12833
  ] at hbad
  tauto

theorem fin15Anchored_clause19676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12833
  ] at hbad
  tauto

theorem fin15Anchored_clause19677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom0807 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0807 Fin15AnchoredAtom2683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12833
  ] at hbad
  tauto

theorem fin15Anchored_clause19678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2683 chi ∧
      ¬Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1682 Fin15AnchoredAtom2683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12833
  ] at hbad
  tauto

theorem fin15Anchored_clause19679 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2683 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0733 chi ∧
      Fin15AnchoredAtom0807 chi ∧
      Fin15AnchoredAtom1682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom0724 Fin15AnchoredAtom0733
    Fin15AnchoredAtom0807 Fin15AnchoredAtom1682 Fin15AnchoredAtom2683 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12833
  ] at hbad
  tauto

theorem fin15Anchored_clause19680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom0723 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom2684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21025
  ] at hbad
  tauto

theorem fin15Anchored_clause19681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21025
  ] at hbad
  tauto

theorem fin15Anchored_clause19682 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom0734 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0734 Fin15AnchoredAtom2684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21025
  ] at hbad
  tauto

theorem fin15Anchored_clause19683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom0808 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0808 Fin15AnchoredAtom2684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21025
  ] at hbad
  tauto

theorem fin15Anchored_clause19684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2684 chi ∧
      ¬Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1683 Fin15AnchoredAtom2684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21025
  ] at hbad
  tauto

theorem fin15Anchored_clause19685 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2684 chi ∧
      Fin15AnchoredAtom0723 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0734 chi ∧
      Fin15AnchoredAtom0808 chi ∧
      Fin15AnchoredAtom1683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0723 Fin15AnchoredAtom0725 Fin15AnchoredAtom0734
    Fin15AnchoredAtom0808 Fin15AnchoredAtom1683 Fin15AnchoredAtom2684 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21025
  ] at hbad
  tauto

theorem fin15Anchored_clause19686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom0724 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom2685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25121
  ] at hbad
  tauto

theorem fin15Anchored_clause19687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom0725 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0725 Fin15AnchoredAtom2685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25121
  ] at hbad
  tauto

theorem fin15Anchored_clause19688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom0735 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0735 Fin15AnchoredAtom2685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25121
  ] at hbad
  tauto

theorem fin15Anchored_clause19689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom0809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0809 Fin15AnchoredAtom2685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25121
  ] at hbad
  tauto

theorem fin15Anchored_clause19690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2685 chi ∧
      ¬Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1684 Fin15AnchoredAtom2685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25121
  ] at hbad
  tauto

theorem fin15Anchored_clause19691 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2685 chi ∧
      Fin15AnchoredAtom0724 chi ∧
      Fin15AnchoredAtom0725 chi ∧
      Fin15AnchoredAtom0735 chi ∧
      Fin15AnchoredAtom0809 chi ∧
      Fin15AnchoredAtom1684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0724 Fin15AnchoredAtom0725 Fin15AnchoredAtom0735
    Fin15AnchoredAtom0809 Fin15AnchoredAtom1684 Fin15AnchoredAtom2685 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25121
  ] at hbad
  tauto

theorem fin15Anchored_clause19692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom2686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07201
  ] at hbad
  tauto

theorem fin15Anchored_clause19693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07201
  ] at hbad
  tauto

theorem fin15Anchored_clause19694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom0730 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0730 Fin15AnchoredAtom2686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07201
  ] at hbad
  tauto

theorem fin15Anchored_clause19695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom0810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0810 Fin15AnchoredAtom2686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07201
  ] at hbad
  tauto

theorem fin15Anchored_clause19696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2686 chi ∧
      ¬Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1685 Fin15AnchoredAtom2686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07201
  ] at hbad
  tauto

theorem fin15Anchored_clause19697 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2686 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0727 chi ∧
      Fin15AnchoredAtom0730 chi ∧
      Fin15AnchoredAtom0810 chi ∧
      Fin15AnchoredAtom1685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom0727 Fin15AnchoredAtom0730
    Fin15AnchoredAtom0810 Fin15AnchoredAtom1685 Fin15AnchoredAtom2686 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07201
  ] at hbad
  tauto

theorem fin15Anchored_clause19698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom0726 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom2687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11297
  ] at hbad
  tauto

theorem fin15Anchored_clause19699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11297
  ] at hbad
  tauto

theorem fin15Anchored_clause19700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom0731 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0731 Fin15AnchoredAtom2687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11297
  ] at hbad
  tauto

theorem fin15Anchored_clause19701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom0811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0811 Fin15AnchoredAtom2687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11297
  ] at hbad
  tauto

theorem fin15Anchored_clause19702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2687 chi ∧
      ¬Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1686 Fin15AnchoredAtom2687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11297
  ] at hbad
  tauto

theorem fin15Anchored_clause19703 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2687 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0728 chi ∧
      Fin15AnchoredAtom0731 chi ∧
      Fin15AnchoredAtom0811 chi ∧
      Fin15AnchoredAtom1686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom0728 Fin15AnchoredAtom0731
    Fin15AnchoredAtom0811 Fin15AnchoredAtom1686 Fin15AnchoredAtom2687 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11297
  ] at hbad
  tauto

theorem fin15Anchored_clause19704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2688 chi ∧
      ¬Fin15AnchoredAtom0729 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0729 Fin15AnchoredAtom2688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19489
  ] at hbad
  tauto

theorem fin15Anchored_clause19705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2688 chi ∧
      ¬Fin15AnchoredAtom0812 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0812 Fin15AnchoredAtom2688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19489
  ] at hbad
  tauto

theorem fin15Anchored_clause19706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2688 chi ∧
      ¬Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1687 Fin15AnchoredAtom2688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19489
  ] at hbad
  tauto

theorem fin15Anchored_clause19707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2688 chi ∧
      Fin15AnchoredAtom0726 chi ∧
      Fin15AnchoredAtom0729 chi ∧
      Fin15AnchoredAtom0732 chi ∧
      Fin15AnchoredAtom0812 chi ∧
      Fin15AnchoredAtom1687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0726 Fin15AnchoredAtom0729 Fin15AnchoredAtom0732
    Fin15AnchoredAtom0812 Fin15AnchoredAtom1687 Fin15AnchoredAtom2688 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19489
  ] at hbad
  tauto

theorem fin15Anchored_clause19708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom0727 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0727 Fin15AnchoredAtom2689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13345
  ] at hbad
  tauto

theorem fin15Anchored_clause19709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom0728 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0728 Fin15AnchoredAtom2689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13345
  ] at hbad
  tauto

theorem fin15Anchored_clause19710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom0733 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0733 Fin15AnchoredAtom2689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13345
  ] at hbad
  tauto

theorem fin15Anchored_clause19711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2689 chi ∧
      ¬Fin15AnchoredAtom0813 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0813 Fin15AnchoredAtom2689 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13345
  ] at hbad
  tauto

end ErdosSzekeres

end
