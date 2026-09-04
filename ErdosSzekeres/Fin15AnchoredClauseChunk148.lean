module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 148. -/

theorem fin15Anchored_clause18944 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom2535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00849
  ] at hbad
  tauto

theorem fin15Anchored_clause18945 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom0743 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0743 Fin15AnchoredAtom2535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00849
  ] at hbad
  tauto

theorem fin15Anchored_clause18946 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2535 chi ∧
      ¬Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1534 Fin15AnchoredAtom2535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00849
  ] at hbad
  tauto

theorem fin15Anchored_clause18947 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2535 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0743 chi ∧
      Fin15AnchoredAtom1534 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom0666 Fin15AnchoredAtom0679
    Fin15AnchoredAtom0743 Fin15AnchoredAtom1534 Fin15AnchoredAtom2535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00849
  ] at hbad
  tauto

theorem fin15Anchored_clause18948 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom2536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01361
  ] at hbad
  tauto

theorem fin15Anchored_clause18949 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01361
  ] at hbad
  tauto

theorem fin15Anchored_clause18950 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom2536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01361
  ] at hbad
  tauto

theorem fin15Anchored_clause18951 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom0744 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0744 Fin15AnchoredAtom2536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01361
  ] at hbad
  tauto

theorem fin15Anchored_clause18952 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2536 chi ∧
      ¬Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1535 Fin15AnchoredAtom2536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01361
  ] at hbad
  tauto

theorem fin15Anchored_clause18953 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2536 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0744 chi ∧
      Fin15AnchoredAtom1535 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom0667 Fin15AnchoredAtom0680
    Fin15AnchoredAtom0744 Fin15AnchoredAtom1535 Fin15AnchoredAtom2536 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01361
  ] at hbad
  tauto

theorem fin15Anchored_clause18954 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom2538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04433
  ] at hbad
  tauto

theorem fin15Anchored_clause18955 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom2538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04433
  ] at hbad
  tauto

theorem fin15Anchored_clause18956 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom2538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04433
  ] at hbad
  tauto

theorem fin15Anchored_clause18957 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom0746 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0746 Fin15AnchoredAtom2538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04433
  ] at hbad
  tauto

theorem fin15Anchored_clause18958 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2538 chi ∧
      ¬Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1537 Fin15AnchoredAtom2538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04433
  ] at hbad
  tauto

theorem fin15Anchored_clause18959 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2538 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0746 chi ∧
      Fin15AnchoredAtom1537 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom0669 Fin15AnchoredAtom0682
    Fin15AnchoredAtom0746 Fin15AnchoredAtom1537 Fin15AnchoredAtom2538 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04433
  ] at hbad
  tauto

theorem fin15Anchored_clause18960 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom2539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08529
  ] at hbad
  tauto

theorem fin15Anchored_clause18961 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom2539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08529
  ] at hbad
  tauto

theorem fin15Anchored_clause18962 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom2539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08529
  ] at hbad
  tauto

theorem fin15Anchored_clause18963 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom0747 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0747 Fin15AnchoredAtom2539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08529
  ] at hbad
  tauto

theorem fin15Anchored_clause18964 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2539 chi ∧
      ¬Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1538 Fin15AnchoredAtom2539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08529
  ] at hbad
  tauto

theorem fin15Anchored_clause18965 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2539 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0747 chi ∧
      Fin15AnchoredAtom1538 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom0670 Fin15AnchoredAtom0683
    Fin15AnchoredAtom0747 Fin15AnchoredAtom1538 Fin15AnchoredAtom2539 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08529
  ] at hbad
  tauto

theorem fin15Anchored_clause18966 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom0665 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom2540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16721
  ] at hbad
  tauto

theorem fin15Anchored_clause18967 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16721
  ] at hbad
  tauto

theorem fin15Anchored_clause18968 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom2540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16721
  ] at hbad
  tauto

theorem fin15Anchored_clause18969 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom0748 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0748 Fin15AnchoredAtom2540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16721
  ] at hbad
  tauto

theorem fin15Anchored_clause18970 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2540 chi ∧
      ¬Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1539 Fin15AnchoredAtom2540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16721
  ] at hbad
  tauto

theorem fin15Anchored_clause18971 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2540 chi ∧
      Fin15AnchoredAtom0665 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0748 chi ∧
      Fin15AnchoredAtom1539 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0665 Fin15AnchoredAtom0671 Fin15AnchoredAtom0684
    Fin15AnchoredAtom0748 Fin15AnchoredAtom1539 Fin15AnchoredAtom2540 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16721
  ] at hbad
  tauto

theorem fin15Anchored_clause18972 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01617
  ] at hbad
  tauto

theorem fin15Anchored_clause18973 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01617
  ] at hbad
  tauto

theorem fin15Anchored_clause18974 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom2541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01617
  ] at hbad
  tauto

theorem fin15Anchored_clause18975 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom0749 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0749 Fin15AnchoredAtom2541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01617
  ] at hbad
  tauto

theorem fin15Anchored_clause18976 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2541 chi ∧
      ¬Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1540 Fin15AnchoredAtom2541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01617
  ] at hbad
  tauto

theorem fin15Anchored_clause18977 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2541 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0749 chi ∧
      Fin15AnchoredAtom1540 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom0667 Fin15AnchoredAtom0685
    Fin15AnchoredAtom0749 Fin15AnchoredAtom1540 Fin15AnchoredAtom2541 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01617
  ] at hbad
  tauto

theorem fin15Anchored_clause18978 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02641
  ] at hbad
  tauto

theorem fin15Anchored_clause18979 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom2542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02641
  ] at hbad
  tauto

theorem fin15Anchored_clause18980 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom0686 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0686 Fin15AnchoredAtom2542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02641
  ] at hbad
  tauto

theorem fin15Anchored_clause18981 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom0750 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0750 Fin15AnchoredAtom2542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02641
  ] at hbad
  tauto

theorem fin15Anchored_clause18982 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2542 chi ∧
      ¬Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1541 Fin15AnchoredAtom2542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02641
  ] at hbad
  tauto

theorem fin15Anchored_clause18983 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2542 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0686 chi ∧
      Fin15AnchoredAtom0750 chi ∧
      Fin15AnchoredAtom1541 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom0668 Fin15AnchoredAtom0686
    Fin15AnchoredAtom0750 Fin15AnchoredAtom1541 Fin15AnchoredAtom2542 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02641
  ] at hbad
  tauto

theorem fin15Anchored_clause18984 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04689
  ] at hbad
  tauto

theorem fin15Anchored_clause18985 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom2543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04689
  ] at hbad
  tauto

theorem fin15Anchored_clause18986 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom2543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04689
  ] at hbad
  tauto

theorem fin15Anchored_clause18987 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom0751 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0751 Fin15AnchoredAtom2543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04689
  ] at hbad
  tauto

theorem fin15Anchored_clause18988 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2543 chi ∧
      ¬Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1542 Fin15AnchoredAtom2543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04689
  ] at hbad
  tauto

theorem fin15Anchored_clause18989 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2543 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0751 chi ∧
      Fin15AnchoredAtom1542 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom0669 Fin15AnchoredAtom0687
    Fin15AnchoredAtom0751 Fin15AnchoredAtom1542 Fin15AnchoredAtom2543 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04689
  ] at hbad
  tauto

theorem fin15Anchored_clause18990 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08785
  ] at hbad
  tauto

theorem fin15Anchored_clause18991 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom2544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08785
  ] at hbad
  tauto

theorem fin15Anchored_clause18992 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom2544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08785
  ] at hbad
  tauto

theorem fin15Anchored_clause18993 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom0752 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0752 Fin15AnchoredAtom2544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08785
  ] at hbad
  tauto

theorem fin15Anchored_clause18994 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2544 chi ∧
      ¬Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1543 Fin15AnchoredAtom2544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08785
  ] at hbad
  tauto

theorem fin15Anchored_clause18995 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2544 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0752 chi ∧
      Fin15AnchoredAtom1543 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom0670 Fin15AnchoredAtom0688
    Fin15AnchoredAtom0752 Fin15AnchoredAtom1543 Fin15AnchoredAtom2544 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08785
  ] at hbad
  tauto

theorem fin15Anchored_clause18996 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom0666 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom2545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16977
  ] at hbad
  tauto

theorem fin15Anchored_clause18997 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16977
  ] at hbad
  tauto

theorem fin15Anchored_clause18998 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom2545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16977
  ] at hbad
  tauto

theorem fin15Anchored_clause18999 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom0753 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0753 Fin15AnchoredAtom2545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16977
  ] at hbad
  tauto

theorem fin15Anchored_clause19000 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2545 chi ∧
      ¬Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1544 Fin15AnchoredAtom2545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16977
  ] at hbad
  tauto

theorem fin15Anchored_clause19001 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2545 chi ∧
      Fin15AnchoredAtom0666 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0753 chi ∧
      Fin15AnchoredAtom1544 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0666 Fin15AnchoredAtom0671 Fin15AnchoredAtom0689
    Fin15AnchoredAtom0753 Fin15AnchoredAtom1544 Fin15AnchoredAtom2545 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16977
  ] at hbad
  tauto

theorem fin15Anchored_clause19002 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03153
  ] at hbad
  tauto

theorem fin15Anchored_clause19003 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom2546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03153
  ] at hbad
  tauto

theorem fin15Anchored_clause19004 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom2546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03153
  ] at hbad
  tauto

theorem fin15Anchored_clause19005 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom0754 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0754 Fin15AnchoredAtom2546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03153
  ] at hbad
  tauto

theorem fin15Anchored_clause19006 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2546 chi ∧
      ¬Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1545 Fin15AnchoredAtom2546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03153
  ] at hbad
  tauto

theorem fin15Anchored_clause19007 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2546 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0690 chi ∧
      Fin15AnchoredAtom0754 chi ∧
      Fin15AnchoredAtom1545 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom0668 Fin15AnchoredAtom0690
    Fin15AnchoredAtom0754 Fin15AnchoredAtom1545 Fin15AnchoredAtom2546 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03153
  ] at hbad
  tauto

theorem fin15Anchored_clause19008 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2547 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05201
  ] at hbad
  tauto

theorem fin15Anchored_clause19009 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom2547 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05201
  ] at hbad
  tauto

theorem fin15Anchored_clause19010 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom2547 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05201
  ] at hbad
  tauto

theorem fin15Anchored_clause19011 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom0755 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0755 Fin15AnchoredAtom2547 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05201
  ] at hbad
  tauto

theorem fin15Anchored_clause19012 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2547 chi ∧
      ¬Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1546 Fin15AnchoredAtom2547 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05201
  ] at hbad
  tauto

theorem fin15Anchored_clause19013 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2547 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0755 chi ∧
      Fin15AnchoredAtom1546 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom0669 Fin15AnchoredAtom0691
    Fin15AnchoredAtom0755 Fin15AnchoredAtom1546 Fin15AnchoredAtom2547 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05201
  ] at hbad
  tauto

theorem fin15Anchored_clause19014 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09297
  ] at hbad
  tauto

theorem fin15Anchored_clause19015 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom2548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09297
  ] at hbad
  tauto

theorem fin15Anchored_clause19016 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom2548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09297
  ] at hbad
  tauto

theorem fin15Anchored_clause19017 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom0756 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0756 Fin15AnchoredAtom2548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09297
  ] at hbad
  tauto

theorem fin15Anchored_clause19018 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2548 chi ∧
      ¬Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1547 Fin15AnchoredAtom2548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09297
  ] at hbad
  tauto

theorem fin15Anchored_clause19019 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2548 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0756 chi ∧
      Fin15AnchoredAtom1547 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom0670 Fin15AnchoredAtom0692
    Fin15AnchoredAtom0756 Fin15AnchoredAtom1547 Fin15AnchoredAtom2548 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09297
  ] at hbad
  tauto

theorem fin15Anchored_clause19020 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom0667 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom2549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17489
  ] at hbad
  tauto

theorem fin15Anchored_clause19021 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17489
  ] at hbad
  tauto

theorem fin15Anchored_clause19022 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom2549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17489
  ] at hbad
  tauto

theorem fin15Anchored_clause19023 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom0757 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0757 Fin15AnchoredAtom2549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17489
  ] at hbad
  tauto

theorem fin15Anchored_clause19024 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2549 chi ∧
      ¬Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1548 Fin15AnchoredAtom2549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17489
  ] at hbad
  tauto

theorem fin15Anchored_clause19025 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2549 chi ∧
      Fin15AnchoredAtom0667 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0757 chi ∧
      Fin15AnchoredAtom1548 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0667 Fin15AnchoredAtom0671 Fin15AnchoredAtom0693
    Fin15AnchoredAtom0757 Fin15AnchoredAtom1548 Fin15AnchoredAtom2549 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17489
  ] at hbad
  tauto

theorem fin15Anchored_clause19026 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom2550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06225
  ] at hbad
  tauto

theorem fin15Anchored_clause19027 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom2550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06225
  ] at hbad
  tauto

theorem fin15Anchored_clause19028 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom0758 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0758 Fin15AnchoredAtom2550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06225
  ] at hbad
  tauto

theorem fin15Anchored_clause19029 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2550 chi ∧
      ¬Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1549 Fin15AnchoredAtom2550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06225
  ] at hbad
  tauto

theorem fin15Anchored_clause19030 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2550 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0758 chi ∧
      Fin15AnchoredAtom1549 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom0669 Fin15AnchoredAtom0694
    Fin15AnchoredAtom0758 Fin15AnchoredAtom1549 Fin15AnchoredAtom2550 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06225
  ] at hbad
  tauto

theorem fin15Anchored_clause19031 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom2551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10321
  ] at hbad
  tauto

theorem fin15Anchored_clause19032 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom0695 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0695 Fin15AnchoredAtom2551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10321
  ] at hbad
  tauto

theorem fin15Anchored_clause19033 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom0759 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0759 Fin15AnchoredAtom2551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10321
  ] at hbad
  tauto

theorem fin15Anchored_clause19034 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2551 chi ∧
      ¬Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1550 Fin15AnchoredAtom2551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10321
  ] at hbad
  tauto

theorem fin15Anchored_clause19035 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2551 chi ∧
      Fin15AnchoredAtom0668 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0759 chi ∧
      Fin15AnchoredAtom1550 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom0670 Fin15AnchoredAtom0695
    Fin15AnchoredAtom0759 Fin15AnchoredAtom1550 Fin15AnchoredAtom2551 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10321
  ] at hbad
  tauto

theorem fin15Anchored_clause19036 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2552 chi ∧
      ¬Fin15AnchoredAtom0668 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0668 Fin15AnchoredAtom2552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18513
  ] at hbad
  tauto

theorem fin15Anchored_clause19037 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2552 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2552 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18513
  ] at hbad
  tauto

theorem fin15Anchored_clause19038 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom2553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12369
  ] at hbad
  tauto

theorem fin15Anchored_clause19039 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom2553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12369
  ] at hbad
  tauto

theorem fin15Anchored_clause19040 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom2553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12369
  ] at hbad
  tauto

theorem fin15Anchored_clause19041 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom0761 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0761 Fin15AnchoredAtom2553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12369
  ] at hbad
  tauto

theorem fin15Anchored_clause19042 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2553 chi ∧
      ¬Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1552 Fin15AnchoredAtom2553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12369
  ] at hbad
  tauto

theorem fin15Anchored_clause19043 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2553 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0761 chi ∧
      Fin15AnchoredAtom1552 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom0670 Fin15AnchoredAtom0697
    Fin15AnchoredAtom0761 Fin15AnchoredAtom1552 Fin15AnchoredAtom2553 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12369
  ] at hbad
  tauto

theorem fin15Anchored_clause19044 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom0669 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom2554 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20561
  ] at hbad
  tauto

theorem fin15Anchored_clause19045 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2554 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20561
  ] at hbad
  tauto

theorem fin15Anchored_clause19046 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom2554 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20561
  ] at hbad
  tauto

theorem fin15Anchored_clause19047 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom0762 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0762 Fin15AnchoredAtom2554 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20561
  ] at hbad
  tauto

theorem fin15Anchored_clause19048 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2554 chi ∧
      ¬Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1553 Fin15AnchoredAtom2554 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20561
  ] at hbad
  tauto

theorem fin15Anchored_clause19049 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2554 chi ∧
      Fin15AnchoredAtom0669 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0698 chi ∧
      Fin15AnchoredAtom0762 chi ∧
      Fin15AnchoredAtom1553 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0669 Fin15AnchoredAtom0671 Fin15AnchoredAtom0698
    Fin15AnchoredAtom0762 Fin15AnchoredAtom1553 Fin15AnchoredAtom2554 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20561
  ] at hbad
  tauto

theorem fin15Anchored_clause19050 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom0670 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom2555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24657
  ] at hbad
  tauto

theorem fin15Anchored_clause19051 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom0671 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0671 Fin15AnchoredAtom2555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24657
  ] at hbad
  tauto

theorem fin15Anchored_clause19052 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom0699 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0699 Fin15AnchoredAtom2555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24657
  ] at hbad
  tauto

theorem fin15Anchored_clause19053 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom0763 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0763 Fin15AnchoredAtom2555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24657
  ] at hbad
  tauto

theorem fin15Anchored_clause19054 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2555 chi ∧
      ¬Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1554 Fin15AnchoredAtom2555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24657
  ] at hbad
  tauto

theorem fin15Anchored_clause19055 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2555 chi ∧
      Fin15AnchoredAtom0670 chi ∧
      Fin15AnchoredAtom0671 chi ∧
      Fin15AnchoredAtom0699 chi ∧
      Fin15AnchoredAtom0763 chi ∧
      Fin15AnchoredAtom1554 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0670 Fin15AnchoredAtom0671 Fin15AnchoredAtom0699
    Fin15AnchoredAtom0763 Fin15AnchoredAtom1554 Fin15AnchoredAtom2555 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24657
  ] at hbad
  tauto

theorem fin15Anchored_clause19056 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom2556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00913
  ] at hbad
  tauto

theorem fin15Anchored_clause19057 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom2556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00913
  ] at hbad
  tauto

theorem fin15Anchored_clause19058 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom2556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00913
  ] at hbad
  tauto

theorem fin15Anchored_clause19059 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom0764 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0764 Fin15AnchoredAtom2556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00913
  ] at hbad
  tauto

theorem fin15Anchored_clause19060 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2556 chi ∧
      ¬Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1555 Fin15AnchoredAtom2556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00913
  ] at hbad
  tauto

theorem fin15Anchored_clause19061 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2556 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0764 chi ∧
      Fin15AnchoredAtom1555 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom0673 Fin15AnchoredAtom0679
    Fin15AnchoredAtom0764 Fin15AnchoredAtom1555 Fin15AnchoredAtom2556 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00913
  ] at hbad
  tauto

theorem fin15Anchored_clause19062 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom2557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01425
  ] at hbad
  tauto

theorem fin15Anchored_clause19063 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom2557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01425
  ] at hbad
  tauto

theorem fin15Anchored_clause19064 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom2557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01425
  ] at hbad
  tauto

theorem fin15Anchored_clause19065 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom0765 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0765 Fin15AnchoredAtom2557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01425
  ] at hbad
  tauto

theorem fin15Anchored_clause19066 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2557 chi ∧
      ¬Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1556 Fin15AnchoredAtom2557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01425
  ] at hbad
  tauto

theorem fin15Anchored_clause19067 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2557 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0765 chi ∧
      Fin15AnchoredAtom1556 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom0674 Fin15AnchoredAtom0680
    Fin15AnchoredAtom0765 Fin15AnchoredAtom1556 Fin15AnchoredAtom2557 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01425
  ] at hbad
  tauto

theorem fin15Anchored_clause19068 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom2559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04497
  ] at hbad
  tauto

theorem fin15Anchored_clause19069 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom2559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04497
  ] at hbad
  tauto

theorem fin15Anchored_clause19070 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom2559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04497
  ] at hbad
  tauto

theorem fin15Anchored_clause19071 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2559 chi ∧
      ¬Fin15AnchoredAtom0767 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0767 Fin15AnchoredAtom2559 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04497
  ] at hbad
  tauto

end ErdosSzekeres

end
