module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 177. -/

theorem fin15Anchored_clause22656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom3364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08866
  ] at hbad
  tauto

theorem fin15Anchored_clause22657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3364 chi ∧
      ¬Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1648 Fin15AnchoredAtom3364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08866
  ] at hbad
  tauto

theorem fin15Anchored_clause22658 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3364 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1648 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom0999 Fin15AnchoredAtom1010
    Fin15AnchoredAtom1059 Fin15AnchoredAtom1648 Fin15AnchoredAtom3364 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08866
  ] at hbad
  tauto

theorem fin15Anchored_clause22659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom0995 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom3365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17058
  ] at hbad
  tauto

theorem fin15Anchored_clause22660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom3365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17058
  ] at hbad
  tauto

theorem fin15Anchored_clause22661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom3365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17058
  ] at hbad
  tauto

theorem fin15Anchored_clause22662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom3365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17058
  ] at hbad
  tauto

theorem fin15Anchored_clause22663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3365 chi ∧
      ¬Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1649 Fin15AnchoredAtom3365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17058
  ] at hbad
  tauto

theorem fin15Anchored_clause22664 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3365 chi ∧
      Fin15AnchoredAtom0995 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1649 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0995 Fin15AnchoredAtom1000 Fin15AnchoredAtom1011
    Fin15AnchoredAtom1060 Fin15AnchoredAtom1649 Fin15AnchoredAtom3365 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17058
  ] at hbad
  tauto

theorem fin15Anchored_clause22665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3366 chi ∧
      ¬Fin15AnchoredAtom0997 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0997 Fin15AnchoredAtom3366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03234
  ] at hbad
  tauto

theorem fin15Anchored_clause22666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3366 chi ∧
      ¬Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1061 Fin15AnchoredAtom3366 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03234
  ] at hbad
  tauto

theorem fin15Anchored_clause22667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom3367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05282
  ] at hbad
  tauto

theorem fin15Anchored_clause22668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom3367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05282
  ] at hbad
  tauto

theorem fin15Anchored_clause22669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom3367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05282
  ] at hbad
  tauto

theorem fin15Anchored_clause22670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom3367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05282
  ] at hbad
  tauto

theorem fin15Anchored_clause22671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3367 chi ∧
      ¬Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1651 Fin15AnchoredAtom3367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05282
  ] at hbad
  tauto

theorem fin15Anchored_clause22672 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3367 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1651 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom0998 Fin15AnchoredAtom1013
    Fin15AnchoredAtom1062 Fin15AnchoredAtom1651 Fin15AnchoredAtom3367 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05282
  ] at hbad
  tauto

theorem fin15Anchored_clause22673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom3368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09378
  ] at hbad
  tauto

theorem fin15Anchored_clause22674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom3368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09378
  ] at hbad
  tauto

theorem fin15Anchored_clause22675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom3368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09378
  ] at hbad
  tauto

theorem fin15Anchored_clause22676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom3368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09378
  ] at hbad
  tauto

theorem fin15Anchored_clause22677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3368 chi ∧
      ¬Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1652 Fin15AnchoredAtom3368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09378
  ] at hbad
  tauto

theorem fin15Anchored_clause22678 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3368 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1652 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom0999 Fin15AnchoredAtom1014
    Fin15AnchoredAtom1063 Fin15AnchoredAtom1652 Fin15AnchoredAtom3368 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09378
  ] at hbad
  tauto

theorem fin15Anchored_clause22679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom0996 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom3369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17570
  ] at hbad
  tauto

theorem fin15Anchored_clause22680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom3369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17570
  ] at hbad
  tauto

theorem fin15Anchored_clause22681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom3369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17570
  ] at hbad
  tauto

theorem fin15Anchored_clause22682 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17570
  ] at hbad
  tauto

theorem fin15Anchored_clause22683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3369 chi ∧
      ¬Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1653 Fin15AnchoredAtom3369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17570
  ] at hbad
  tauto

theorem fin15Anchored_clause22684 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3369 chi ∧
      Fin15AnchoredAtom0996 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1653 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0996 Fin15AnchoredAtom1000 Fin15AnchoredAtom1015
    Fin15AnchoredAtom1064 Fin15AnchoredAtom1653 Fin15AnchoredAtom3369 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17570
  ] at hbad
  tauto

theorem fin15Anchored_clause22685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom3370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06306
  ] at hbad
  tauto

theorem fin15Anchored_clause22686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom1065 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1065 Fin15AnchoredAtom3370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06306
  ] at hbad
  tauto

theorem fin15Anchored_clause22687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3370 chi ∧
      ¬Fin15AnchoredAtom1654 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1654 Fin15AnchoredAtom3370 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06306
  ] at hbad
  tauto

theorem fin15Anchored_clause22688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3371 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom3371 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10402
  ] at hbad
  tauto

theorem fin15Anchored_clause22689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3372 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom3372 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18594
  ] at hbad
  tauto

theorem fin15Anchored_clause22690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom3373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12450
  ] at hbad
  tauto

theorem fin15Anchored_clause22691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom3373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12450
  ] at hbad
  tauto

theorem fin15Anchored_clause22692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom3373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12450
  ] at hbad
  tauto

theorem fin15Anchored_clause22693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12450
  ] at hbad
  tauto

theorem fin15Anchored_clause22694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3373 chi ∧
      ¬Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1657 Fin15AnchoredAtom3373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12450
  ] at hbad
  tauto

theorem fin15Anchored_clause22695 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3373 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1657 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom0999 Fin15AnchoredAtom1019
    Fin15AnchoredAtom1068 Fin15AnchoredAtom1657 Fin15AnchoredAtom3373 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12450
  ] at hbad
  tauto

theorem fin15Anchored_clause22696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom0998 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom3374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20642
  ] at hbad
  tauto

theorem fin15Anchored_clause22697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom3374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20642
  ] at hbad
  tauto

theorem fin15Anchored_clause22698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom3374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20642
  ] at hbad
  tauto

theorem fin15Anchored_clause22699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20642
  ] at hbad
  tauto

theorem fin15Anchored_clause22700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3374 chi ∧
      ¬Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1658 Fin15AnchoredAtom3374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20642
  ] at hbad
  tauto

theorem fin15Anchored_clause22701 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3374 chi ∧
      Fin15AnchoredAtom0998 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1658 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0998 Fin15AnchoredAtom1000 Fin15AnchoredAtom1020
    Fin15AnchoredAtom1069 Fin15AnchoredAtom1658 Fin15AnchoredAtom3374 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20642
  ] at hbad
  tauto

theorem fin15Anchored_clause22702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom0999 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom3375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24738
  ] at hbad
  tauto

theorem fin15Anchored_clause22703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom1000 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1000 Fin15AnchoredAtom3375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24738
  ] at hbad
  tauto

theorem fin15Anchored_clause22704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom3375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24738
  ] at hbad
  tauto

theorem fin15Anchored_clause22705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24738
  ] at hbad
  tauto

theorem fin15Anchored_clause22706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3375 chi ∧
      ¬Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1659 Fin15AnchoredAtom3375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24738
  ] at hbad
  tauto

theorem fin15Anchored_clause22707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3375 chi ∧
      Fin15AnchoredAtom0999 chi ∧
      Fin15AnchoredAtom1000 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1659 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0999 Fin15AnchoredAtom1000 Fin15AnchoredAtom1021
    Fin15AnchoredAtom1070 Fin15AnchoredAtom1659 Fin15AnchoredAtom3375 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24738
  ] at hbad
  tauto

theorem fin15Anchored_clause22708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom3376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01826
  ] at hbad
  tauto

theorem fin15Anchored_clause22709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom3376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01826
  ] at hbad
  tauto

theorem fin15Anchored_clause22710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom3376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01826
  ] at hbad
  tauto

theorem fin15Anchored_clause22711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom3376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01826
  ] at hbad
  tauto

theorem fin15Anchored_clause22712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3376 chi ∧
      ¬Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1660 Fin15AnchoredAtom3376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01826
  ] at hbad
  tauto

theorem fin15Anchored_clause22713 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3376 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1660 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom1002 Fin15AnchoredAtom1007
    Fin15AnchoredAtom1071 Fin15AnchoredAtom1660 Fin15AnchoredAtom3376 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01826
  ] at hbad
  tauto

theorem fin15Anchored_clause22714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom3378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04898
  ] at hbad
  tauto

theorem fin15Anchored_clause22715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1004 Fin15AnchoredAtom3378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04898
  ] at hbad
  tauto

theorem fin15Anchored_clause22716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom3378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04898
  ] at hbad
  tauto

theorem fin15Anchored_clause22717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom3378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04898
  ] at hbad
  tauto

theorem fin15Anchored_clause22718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3378 chi ∧
      ¬Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1662 Fin15AnchoredAtom3378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04898
  ] at hbad
  tauto

theorem fin15Anchored_clause22719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3378 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1662 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom1004 Fin15AnchoredAtom1009
    Fin15AnchoredAtom1073 Fin15AnchoredAtom1662 Fin15AnchoredAtom3378 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04898
  ] at hbad
  tauto

theorem fin15Anchored_clause22720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom3379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08994
  ] at hbad
  tauto

theorem fin15Anchored_clause22721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom3379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08994
  ] at hbad
  tauto

theorem fin15Anchored_clause22722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom3379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08994
  ] at hbad
  tauto

theorem fin15Anchored_clause22723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3379 chi ∧
      ¬Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1663 Fin15AnchoredAtom3379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08994
  ] at hbad
  tauto

theorem fin15Anchored_clause22724 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3379 chi ∧
      Fin15AnchoredAtom1001 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1663 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom1005 Fin15AnchoredAtom1010
    Fin15AnchoredAtom1074 Fin15AnchoredAtom1663 Fin15AnchoredAtom3379 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08994
  ] at hbad
  tauto

theorem fin15Anchored_clause22725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1001 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1001 Fin15AnchoredAtom3380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17186
  ] at hbad
  tauto

theorem fin15Anchored_clause22726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1006 Fin15AnchoredAtom3380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17186
  ] at hbad
  tauto

theorem fin15Anchored_clause22727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom3380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17186
  ] at hbad
  tauto

theorem fin15Anchored_clause22728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1075 Fin15AnchoredAtom3380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17186
  ] at hbad
  tauto

theorem fin15Anchored_clause22729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3380 chi ∧
      ¬Fin15AnchoredAtom1664 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1664 Fin15AnchoredAtom3380 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17186
  ] at hbad
  tauto

theorem fin15Anchored_clause22730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom3382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05410
  ] at hbad
  tauto

theorem fin15Anchored_clause22731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom1004 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1004 Fin15AnchoredAtom3382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05410
  ] at hbad
  tauto

theorem fin15Anchored_clause22732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom3382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05410
  ] at hbad
  tauto

theorem fin15Anchored_clause22733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3382 chi ∧
      ¬Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1666 Fin15AnchoredAtom3382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05410
  ] at hbad
  tauto

theorem fin15Anchored_clause22734 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3382 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom1004 Fin15AnchoredAtom1013
    Fin15AnchoredAtom1077 Fin15AnchoredAtom1666 Fin15AnchoredAtom3382 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05410
  ] at hbad
  tauto

theorem fin15Anchored_clause22735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom3383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09506
  ] at hbad
  tauto

theorem fin15Anchored_clause22736 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom3383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09506
  ] at hbad
  tauto

theorem fin15Anchored_clause22737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom3383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09506
  ] at hbad
  tauto

theorem fin15Anchored_clause22738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom3383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09506
  ] at hbad
  tauto

theorem fin15Anchored_clause22739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3383 chi ∧
      ¬Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1667 Fin15AnchoredAtom3383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09506
  ] at hbad
  tauto

theorem fin15Anchored_clause22740 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3383 chi ∧
      Fin15AnchoredAtom1002 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom1005 Fin15AnchoredAtom1014
    Fin15AnchoredAtom1078 Fin15AnchoredAtom1667 Fin15AnchoredAtom3383 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09506
  ] at hbad
  tauto

theorem fin15Anchored_clause22741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom1002 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1002 Fin15AnchoredAtom3384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17698
  ] at hbad
  tauto

theorem fin15Anchored_clause22742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom3384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17698
  ] at hbad
  tauto

theorem fin15Anchored_clause22743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1079 Fin15AnchoredAtom3384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17698
  ] at hbad
  tauto

theorem fin15Anchored_clause22744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3384 chi ∧
      ¬Fin15AnchoredAtom1668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1668 Fin15AnchoredAtom3384 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17698
  ] at hbad
  tauto

theorem fin15Anchored_clause22745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom3388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12578
  ] at hbad
  tauto

theorem fin15Anchored_clause22746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom1019 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1019 Fin15AnchoredAtom3388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12578
  ] at hbad
  tauto

theorem fin15Anchored_clause22747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3388 chi ∧
      ¬Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1672 Fin15AnchoredAtom3388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12578
  ] at hbad
  tauto

theorem fin15Anchored_clause22748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3388 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1019 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1004 Fin15AnchoredAtom1005 Fin15AnchoredAtom1019
    Fin15AnchoredAtom1083 Fin15AnchoredAtom1672 Fin15AnchoredAtom3388 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12578
  ] at hbad
  tauto

theorem fin15Anchored_clause22749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1006 Fin15AnchoredAtom3389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20770
  ] at hbad
  tauto

theorem fin15Anchored_clause22750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom1020 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1020 Fin15AnchoredAtom3389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20770
  ] at hbad
  tauto

theorem fin15Anchored_clause22751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3389 chi ∧
      ¬Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1673 Fin15AnchoredAtom3389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20770
  ] at hbad
  tauto

theorem fin15Anchored_clause22752 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3389 chi ∧
      Fin15AnchoredAtom1004 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1020 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1004 Fin15AnchoredAtom1006 Fin15AnchoredAtom1020
    Fin15AnchoredAtom1084 Fin15AnchoredAtom1673 Fin15AnchoredAtom3389 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20770
  ] at hbad
  tauto

theorem fin15Anchored_clause22753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom1005 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom3390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24866
  ] at hbad
  tauto

theorem fin15Anchored_clause22754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom1006 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1006 Fin15AnchoredAtom3390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24866
  ] at hbad
  tauto

theorem fin15Anchored_clause22755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom1021 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1021 Fin15AnchoredAtom3390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24866
  ] at hbad
  tauto

theorem fin15Anchored_clause22756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3390 chi ∧
      ¬Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1674 Fin15AnchoredAtom3390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24866
  ] at hbad
  tauto

theorem fin15Anchored_clause22757 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3390 chi ∧
      Fin15AnchoredAtom1005 chi ∧
      Fin15AnchoredAtom1006 chi ∧
      Fin15AnchoredAtom1021 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1005 Fin15AnchoredAtom1006 Fin15AnchoredAtom1021
    Fin15AnchoredAtom1085 Fin15AnchoredAtom1674 Fin15AnchoredAtom3390 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24866
  ] at hbad
  tauto

theorem fin15Anchored_clause22758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom3391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03618
  ] at hbad
  tauto

theorem fin15Anchored_clause22759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom1008 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1008 Fin15AnchoredAtom3391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03618
  ] at hbad
  tauto

theorem fin15Anchored_clause22760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3391 chi ∧
      ¬Fin15AnchoredAtom1675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1675 Fin15AnchoredAtom3391 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03618
  ] at hbad
  tauto

theorem fin15Anchored_clause22761 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom3392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05666
  ] at hbad
  tauto

theorem fin15Anchored_clause22762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom3392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05666
  ] at hbad
  tauto

theorem fin15Anchored_clause22763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1013 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1013 Fin15AnchoredAtom3392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05666
  ] at hbad
  tauto

theorem fin15Anchored_clause22764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05666
  ] at hbad
  tauto

theorem fin15Anchored_clause22765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3392 chi ∧
      ¬Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1676 Fin15AnchoredAtom3392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05666
  ] at hbad
  tauto

theorem fin15Anchored_clause22766 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3392 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1009 chi ∧
      Fin15AnchoredAtom1013 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom1009 Fin15AnchoredAtom1013
    Fin15AnchoredAtom1087 Fin15AnchoredAtom1676 Fin15AnchoredAtom3392 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05666
  ] at hbad
  tauto

theorem fin15Anchored_clause22767 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom3393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09762
  ] at hbad
  tauto

theorem fin15Anchored_clause22768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom3393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09762
  ] at hbad
  tauto

theorem fin15Anchored_clause22769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1014 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1014 Fin15AnchoredAtom3393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09762
  ] at hbad
  tauto

theorem fin15Anchored_clause22770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09762
  ] at hbad
  tauto

theorem fin15Anchored_clause22771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3393 chi ∧
      ¬Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1677 Fin15AnchoredAtom3393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09762
  ] at hbad
  tauto

theorem fin15Anchored_clause22772 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3393 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1010 chi ∧
      Fin15AnchoredAtom1014 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom1010 Fin15AnchoredAtom1014
    Fin15AnchoredAtom1088 Fin15AnchoredAtom1677 Fin15AnchoredAtom3393 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09762
  ] at hbad
  tauto

theorem fin15Anchored_clause22773 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1007 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom3394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17954
  ] at hbad
  tauto

theorem fin15Anchored_clause22774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom3394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17954
  ] at hbad
  tauto

theorem fin15Anchored_clause22775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1015 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1015 Fin15AnchoredAtom3394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17954
  ] at hbad
  tauto

theorem fin15Anchored_clause22776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom3394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17954
  ] at hbad
  tauto

theorem fin15Anchored_clause22777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3394 chi ∧
      ¬Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1678 Fin15AnchoredAtom3394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17954
  ] at hbad
  tauto

theorem fin15Anchored_clause22778 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3394 chi ∧
      Fin15AnchoredAtom1007 chi ∧
      Fin15AnchoredAtom1011 chi ∧
      Fin15AnchoredAtom1015 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1007 Fin15AnchoredAtom1011 Fin15AnchoredAtom1015
    Fin15AnchoredAtom1089 Fin15AnchoredAtom1678 Fin15AnchoredAtom3394 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17954
  ] at hbad
  tauto

theorem fin15Anchored_clause22779 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom1008 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1008 Fin15AnchoredAtom3395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06690
  ] at hbad
  tauto

theorem fin15Anchored_clause22780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom1009 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1009 Fin15AnchoredAtom3395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06690
  ] at hbad
  tauto

theorem fin15Anchored_clause22781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3395 chi ∧
      ¬Fin15AnchoredAtom1679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1679 Fin15AnchoredAtom3395 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06690
  ] at hbad
  tauto

theorem fin15Anchored_clause22782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3396 chi ∧
      ¬Fin15AnchoredAtom1010 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1010 Fin15AnchoredAtom3396 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10786
  ] at hbad
  tauto

theorem fin15Anchored_clause22783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3397 chi ∧
      ¬Fin15AnchoredAtom1011 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1011 Fin15AnchoredAtom3397 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18978
  ] at hbad
  tauto

end ErdosSzekeres

end
