module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 130. -/

theorem fin15Anchored_clause16640 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2061 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0774 chi ∧
      Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom0512 Fin15AnchoredAtom0523
    Fin15AnchoredAtom0774 Fin15AnchoredAtom1060 Fin15AnchoredAtom2061 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17027
  ] at hbad
  tauto

theorem fin15Anchored_clause16641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom2062 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03203
  ] at hbad
  tauto

theorem fin15Anchored_clause16642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2062 chi ∧
      ¬Fin15AnchoredAtom0775 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0775 Fin15AnchoredAtom2062 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03203
  ] at hbad
  tauto

theorem fin15Anchored_clause16643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom2063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05251
  ] at hbad
  tauto

theorem fin15Anchored_clause16644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom2063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05251
  ] at hbad
  tauto

theorem fin15Anchored_clause16645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom2063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05251
  ] at hbad
  tauto

theorem fin15Anchored_clause16646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom0776 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0776 Fin15AnchoredAtom2063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05251
  ] at hbad
  tauto

theorem fin15Anchored_clause16647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2063 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom2063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05251
  ] at hbad
  tauto

theorem fin15Anchored_clause16648 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2063 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0776 chi ∧
      Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom0510 Fin15AnchoredAtom0525
    Fin15AnchoredAtom0776 Fin15AnchoredAtom1062 Fin15AnchoredAtom2063 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05251
  ] at hbad
  tauto

theorem fin15Anchored_clause16649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom2064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09347
  ] at hbad
  tauto

theorem fin15Anchored_clause16650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom2064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09347
  ] at hbad
  tauto

theorem fin15Anchored_clause16651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom2064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09347
  ] at hbad
  tauto

theorem fin15Anchored_clause16652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom0777 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0777 Fin15AnchoredAtom2064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09347
  ] at hbad
  tauto

theorem fin15Anchored_clause16653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2064 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom2064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09347
  ] at hbad
  tauto

theorem fin15Anchored_clause16654 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2064 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0777 chi ∧
      Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom0511 Fin15AnchoredAtom0526
    Fin15AnchoredAtom0777 Fin15AnchoredAtom1063 Fin15AnchoredAtom2064 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09347
  ] at hbad
  tauto

theorem fin15Anchored_clause16655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom2065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17539
  ] at hbad
  tauto

theorem fin15Anchored_clause16656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom2065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17539
  ] at hbad
  tauto

theorem fin15Anchored_clause16657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom2065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17539
  ] at hbad
  tauto

theorem fin15Anchored_clause16658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom0778 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0778 Fin15AnchoredAtom2065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17539
  ] at hbad
  tauto

theorem fin15Anchored_clause16659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2065 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom2065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17539
  ] at hbad
  tauto

theorem fin15Anchored_clause16660 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2065 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0778 chi ∧
      Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom0512 Fin15AnchoredAtom0527
    Fin15AnchoredAtom0778 Fin15AnchoredAtom1064 Fin15AnchoredAtom2065 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17539
  ] at hbad
  tauto

theorem fin15Anchored_clause16661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom2066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06275
  ] at hbad
  tauto

theorem fin15Anchored_clause16662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom0528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0528 Fin15AnchoredAtom2066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06275
  ] at hbad
  tauto

theorem fin15Anchored_clause16663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2066 chi ∧
      ¬Fin15AnchoredAtom0779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0779 Fin15AnchoredAtom2066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06275
  ] at hbad
  tauto

theorem fin15Anchored_clause16664 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2066 chi ∧
      Fin15AnchoredAtom0509 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0779 chi ∧
      Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0509 Fin15AnchoredAtom0510 Fin15AnchoredAtom0528
    Fin15AnchoredAtom0779 Fin15AnchoredAtom1065 Fin15AnchoredAtom2066 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06275
  ] at hbad
  tauto

theorem fin15Anchored_clause16665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom2067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10371
  ] at hbad
  tauto

theorem fin15Anchored_clause16666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom0529 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0529 Fin15AnchoredAtom2067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10371
  ] at hbad
  tauto

theorem fin15Anchored_clause16667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2067 chi ∧
      ¬Fin15AnchoredAtom0780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0780 Fin15AnchoredAtom2067 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10371
  ] at hbad
  tauto

theorem fin15Anchored_clause16668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom0509 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0509 Fin15AnchoredAtom2068 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18563
  ] at hbad
  tauto

theorem fin15Anchored_clause16669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2068 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom2068 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18563
  ] at hbad
  tauto

theorem fin15Anchored_clause16670 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2068 chi ∧
      Fin15AnchoredAtom0509 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0781 chi ∧
      Fin15AnchoredAtom1067 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0509 Fin15AnchoredAtom0512 Fin15AnchoredAtom0530
    Fin15AnchoredAtom0781 Fin15AnchoredAtom1067 Fin15AnchoredAtom2068 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18563
  ] at hbad
  tauto

theorem fin15Anchored_clause16671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom2069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12419
  ] at hbad
  tauto

theorem fin15Anchored_clause16672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom2069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12419
  ] at hbad
  tauto

theorem fin15Anchored_clause16673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom2069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12419
  ] at hbad
  tauto

theorem fin15Anchored_clause16674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom0782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0782 Fin15AnchoredAtom2069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12419
  ] at hbad
  tauto

theorem fin15Anchored_clause16675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2069 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom2069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12419
  ] at hbad
  tauto

theorem fin15Anchored_clause16676 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2069 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0782 chi ∧
      Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom0511 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0782 Fin15AnchoredAtom1068 Fin15AnchoredAtom2069 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12419
  ] at hbad
  tauto

theorem fin15Anchored_clause16677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom2070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20611
  ] at hbad
  tauto

theorem fin15Anchored_clause16678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom2070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20611
  ] at hbad
  tauto

theorem fin15Anchored_clause16679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom2070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20611
  ] at hbad
  tauto

theorem fin15Anchored_clause16680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom0783 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0783 Fin15AnchoredAtom2070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20611
  ] at hbad
  tauto

theorem fin15Anchored_clause16681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2070 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom2070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20611
  ] at hbad
  tauto

theorem fin15Anchored_clause16682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2070 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0783 chi ∧
      Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom0512 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0783 Fin15AnchoredAtom1069 Fin15AnchoredAtom2070 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20611
  ] at hbad
  tauto

theorem fin15Anchored_clause16683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom2071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24707
  ] at hbad
  tauto

theorem fin15Anchored_clause16684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom2071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24707
  ] at hbad
  tauto

theorem fin15Anchored_clause16685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom2071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24707
  ] at hbad
  tauto

theorem fin15Anchored_clause16686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom0784 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0784 Fin15AnchoredAtom2071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24707
  ] at hbad
  tauto

theorem fin15Anchored_clause16687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2071 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom2071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24707
  ] at hbad
  tauto

theorem fin15Anchored_clause16688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2071 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0784 chi ∧
      Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom0512 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0784 Fin15AnchoredAtom1070 Fin15AnchoredAtom2071 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24707
  ] at hbad
  tauto

theorem fin15Anchored_clause16689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom2072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01795
  ] at hbad
  tauto

theorem fin15Anchored_clause16690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom2072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01795
  ] at hbad
  tauto

theorem fin15Anchored_clause16691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom2072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01795
  ] at hbad
  tauto

theorem fin15Anchored_clause16692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom0785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0785 Fin15AnchoredAtom2072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01795
  ] at hbad
  tauto

theorem fin15Anchored_clause16693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2072 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom2072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01795
  ] at hbad
  tauto

theorem fin15Anchored_clause16694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2072 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0785 chi ∧
      Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom0514 Fin15AnchoredAtom0519
    Fin15AnchoredAtom0785 Fin15AnchoredAtom1071 Fin15AnchoredAtom2072 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01795
  ] at hbad
  tauto

theorem fin15Anchored_clause16695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom2074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04867
  ] at hbad
  tauto

theorem fin15Anchored_clause16696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom2074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04867
  ] at hbad
  tauto

theorem fin15Anchored_clause16697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom2074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04867
  ] at hbad
  tauto

theorem fin15Anchored_clause16698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom0787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0787 Fin15AnchoredAtom2074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04867
  ] at hbad
  tauto

theorem fin15Anchored_clause16699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2074 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom2074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04867
  ] at hbad
  tauto

theorem fin15Anchored_clause16700 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2074 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0787 chi ∧
      Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom0516 Fin15AnchoredAtom0521
    Fin15AnchoredAtom0787 Fin15AnchoredAtom1073 Fin15AnchoredAtom2074 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04867
  ] at hbad
  tauto

theorem fin15Anchored_clause16701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom2075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08963
  ] at hbad
  tauto

theorem fin15Anchored_clause16702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom2075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08963
  ] at hbad
  tauto

theorem fin15Anchored_clause16703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom0788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0788 Fin15AnchoredAtom2075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08963
  ] at hbad
  tauto

theorem fin15Anchored_clause16704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2075 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1074 Fin15AnchoredAtom2075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08963
  ] at hbad
  tauto

theorem fin15Anchored_clause16705 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2075 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0788 chi ∧
      Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom0517 Fin15AnchoredAtom0522
    Fin15AnchoredAtom0788 Fin15AnchoredAtom1074 Fin15AnchoredAtom2075 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08963
  ] at hbad
  tauto

theorem fin15Anchored_clause16706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom2076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17155
  ] at hbad
  tauto

theorem fin15Anchored_clause16707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom0518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0518 Fin15AnchoredAtom2076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17155
  ] at hbad
  tauto

theorem fin15Anchored_clause16708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom2076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17155
  ] at hbad
  tauto

theorem fin15Anchored_clause16709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2076 chi ∧
      ¬Fin15AnchoredAtom0789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0789 Fin15AnchoredAtom2076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17155
  ] at hbad
  tauto

theorem fin15Anchored_clause16710 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2076 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0789 chi ∧
      Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom0518 Fin15AnchoredAtom0523
    Fin15AnchoredAtom0789 Fin15AnchoredAtom1075 Fin15AnchoredAtom2076 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17155
  ] at hbad
  tauto

theorem fin15Anchored_clause16711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom2078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05379
  ] at hbad
  tauto

theorem fin15Anchored_clause16712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom2078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05379
  ] at hbad
  tauto

theorem fin15Anchored_clause16713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom2078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05379
  ] at hbad
  tauto

theorem fin15Anchored_clause16714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom0791 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0791 Fin15AnchoredAtom2078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05379
  ] at hbad
  tauto

theorem fin15Anchored_clause16715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2078 chi ∧
      ¬Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1077 Fin15AnchoredAtom2078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05379
  ] at hbad
  tauto

theorem fin15Anchored_clause16716 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2078 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0791 chi ∧
      Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom0516 Fin15AnchoredAtom0525
    Fin15AnchoredAtom0791 Fin15AnchoredAtom1077 Fin15AnchoredAtom2078 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05379
  ] at hbad
  tauto

theorem fin15Anchored_clause16717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom2079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09475
  ] at hbad
  tauto

theorem fin15Anchored_clause16718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0517 Fin15AnchoredAtom2079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09475
  ] at hbad
  tauto

theorem fin15Anchored_clause16719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom2079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09475
  ] at hbad
  tauto

theorem fin15Anchored_clause16720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom0792 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0792 Fin15AnchoredAtom2079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09475
  ] at hbad
  tauto

theorem fin15Anchored_clause16721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2079 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom2079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09475
  ] at hbad
  tauto

theorem fin15Anchored_clause16722 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2079 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0792 chi ∧
      Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom0517 Fin15AnchoredAtom0526
    Fin15AnchoredAtom0792 Fin15AnchoredAtom1078 Fin15AnchoredAtom2079 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09475
  ] at hbad
  tauto

theorem fin15Anchored_clause16723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom2080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17667
  ] at hbad
  tauto

theorem fin15Anchored_clause16724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom2080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17667
  ] at hbad
  tauto

theorem fin15Anchored_clause16725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2080 chi ∧
      ¬Fin15AnchoredAtom0793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0793 Fin15AnchoredAtom2080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17667
  ] at hbad
  tauto

theorem fin15Anchored_clause16726 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2080 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0793 chi ∧
      Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom0518 Fin15AnchoredAtom0527
    Fin15AnchoredAtom0793 Fin15AnchoredAtom1079 Fin15AnchoredAtom2080 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17667
  ] at hbad
  tauto

theorem fin15Anchored_clause16727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom2084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12547
  ] at hbad
  tauto

theorem fin15Anchored_clause16728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0517 Fin15AnchoredAtom2084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12547
  ] at hbad
  tauto

theorem fin15Anchored_clause16729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom0797 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0797 Fin15AnchoredAtom2084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12547
  ] at hbad
  tauto

theorem fin15Anchored_clause16730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2084 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1083 Fin15AnchoredAtom2084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12547
  ] at hbad
  tauto

theorem fin15Anchored_clause16731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2084 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0797 chi ∧
      Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom0517 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0797 Fin15AnchoredAtom1083 Fin15AnchoredAtom2084 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12547
  ] at hbad
  tauto

theorem fin15Anchored_clause16732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom0516 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom2085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20739
  ] at hbad
  tauto

theorem fin15Anchored_clause16733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom0518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0518 Fin15AnchoredAtom2085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20739
  ] at hbad
  tauto

theorem fin15Anchored_clause16734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom2085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20739
  ] at hbad
  tauto

theorem fin15Anchored_clause16735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2085 chi ∧
      ¬Fin15AnchoredAtom0798 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0798 Fin15AnchoredAtom2085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20739
  ] at hbad
  tauto

theorem fin15Anchored_clause16736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2085 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0798 chi ∧
      Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0516 Fin15AnchoredAtom0518 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0798 Fin15AnchoredAtom1084 Fin15AnchoredAtom2085 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20739
  ] at hbad
  tauto

theorem fin15Anchored_clause16737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0517 Fin15AnchoredAtom2086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24835
  ] at hbad
  tauto

theorem fin15Anchored_clause16738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom0518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0518 Fin15AnchoredAtom2086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24835
  ] at hbad
  tauto

theorem fin15Anchored_clause16739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom2086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24835
  ] at hbad
  tauto

theorem fin15Anchored_clause16740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom0799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0799 Fin15AnchoredAtom2086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24835
  ] at hbad
  tauto

theorem fin15Anchored_clause16741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2086 chi ∧
      ¬Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1085 Fin15AnchoredAtom2086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24835
  ] at hbad
  tauto

theorem fin15Anchored_clause16742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2086 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0799 chi ∧
      Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0517 Fin15AnchoredAtom0518 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0799 Fin15AnchoredAtom1085 Fin15AnchoredAtom2086 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24835
  ] at hbad
  tauto

theorem fin15Anchored_clause16743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom2087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03587
  ] at hbad
  tauto

theorem fin15Anchored_clause16744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2087 chi ∧
      ¬Fin15AnchoredAtom0800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0800 Fin15AnchoredAtom2087 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03587
  ] at hbad
  tauto

theorem fin15Anchored_clause16745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom2088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05635
  ] at hbad
  tauto

theorem fin15Anchored_clause16746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom2088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05635
  ] at hbad
  tauto

theorem fin15Anchored_clause16747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom2088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05635
  ] at hbad
  tauto

theorem fin15Anchored_clause16748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom0801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0801 Fin15AnchoredAtom2088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05635
  ] at hbad
  tauto

theorem fin15Anchored_clause16749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2088 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom2088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05635
  ] at hbad
  tauto

theorem fin15Anchored_clause16750 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2088 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0801 chi ∧
      Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom0521 Fin15AnchoredAtom0525
    Fin15AnchoredAtom0801 Fin15AnchoredAtom1087 Fin15AnchoredAtom2088 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05635
  ] at hbad
  tauto

theorem fin15Anchored_clause16751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom2089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09731
  ] at hbad
  tauto

theorem fin15Anchored_clause16752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom2089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09731
  ] at hbad
  tauto

theorem fin15Anchored_clause16753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom2089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09731
  ] at hbad
  tauto

theorem fin15Anchored_clause16754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom0802 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0802 Fin15AnchoredAtom2089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09731
  ] at hbad
  tauto

theorem fin15Anchored_clause16755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2089 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom2089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09731
  ] at hbad
  tauto

theorem fin15Anchored_clause16756 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2089 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0802 chi ∧
      Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom0522 Fin15AnchoredAtom0526
    Fin15AnchoredAtom0802 Fin15AnchoredAtom1088 Fin15AnchoredAtom2089 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09731
  ] at hbad
  tauto

theorem fin15Anchored_clause16757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom2090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17923
  ] at hbad
  tauto

theorem fin15Anchored_clause16758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom2090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17923
  ] at hbad
  tauto

theorem fin15Anchored_clause16759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom2090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17923
  ] at hbad
  tauto

theorem fin15Anchored_clause16760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom0803 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0803 Fin15AnchoredAtom2090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17923
  ] at hbad
  tauto

theorem fin15Anchored_clause16761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2090 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom2090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17923
  ] at hbad
  tauto

theorem fin15Anchored_clause16762 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2090 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0803 chi ∧
      Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom0523 Fin15AnchoredAtom0527
    Fin15AnchoredAtom0803 Fin15AnchoredAtom1089 Fin15AnchoredAtom2090 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17923
  ] at hbad
  tauto

theorem fin15Anchored_clause16763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom0520 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0520 Fin15AnchoredAtom2091 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06659
  ] at hbad
  tauto

theorem fin15Anchored_clause16764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom2091 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06659
  ] at hbad
  tauto

theorem fin15Anchored_clause16765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom0528 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0528 Fin15AnchoredAtom2091 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06659
  ] at hbad
  tauto

theorem fin15Anchored_clause16766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom0804 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0804 Fin15AnchoredAtom2091 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06659
  ] at hbad
  tauto

theorem fin15Anchored_clause16767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2091 chi ∧
      ¬Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1090 Fin15AnchoredAtom2091 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06659
  ] at hbad
  tauto

end ErdosSzekeres

end
