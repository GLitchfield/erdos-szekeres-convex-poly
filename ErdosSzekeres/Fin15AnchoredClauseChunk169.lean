module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 169. -/

theorem fin15Anchored_clause21632 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3136 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1035 chi ∧
      Fin15AnchoredAtom1420 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom0908 Fin15AnchoredAtom0926
    Fin15AnchoredAtom1035 Fin15AnchoredAtom1420 Fin15AnchoredAtom3136 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01610
  ] at hbad
  tauto

theorem fin15Anchored_clause21633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3137 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom3137 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02634
  ] at hbad
  tauto

theorem fin15Anchored_clause21634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3137 chi ∧
      ¬Fin15AnchoredAtom1421 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1421 Fin15AnchoredAtom3137 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02634
  ] at hbad
  tauto

theorem fin15Anchored_clause21635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom3138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04682
  ] at hbad
  tauto

theorem fin15Anchored_clause21636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom3138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04682
  ] at hbad
  tauto

theorem fin15Anchored_clause21637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom3138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04682
  ] at hbad
  tauto

theorem fin15Anchored_clause21638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom1037 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1037 Fin15AnchoredAtom3138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04682
  ] at hbad
  tauto

theorem fin15Anchored_clause21639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3138 chi ∧
      ¬Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1422 Fin15AnchoredAtom3138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04682
  ] at hbad
  tauto

theorem fin15Anchored_clause21640 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3138 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1037 chi ∧
      Fin15AnchoredAtom1422 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom0910 Fin15AnchoredAtom0928
    Fin15AnchoredAtom1037 Fin15AnchoredAtom1422 Fin15AnchoredAtom3138 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04682
  ] at hbad
  tauto

theorem fin15Anchored_clause21641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom3139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08778
  ] at hbad
  tauto

theorem fin15Anchored_clause21642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom3139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08778
  ] at hbad
  tauto

theorem fin15Anchored_clause21643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom3139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08778
  ] at hbad
  tauto

theorem fin15Anchored_clause21644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom1038 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1038 Fin15AnchoredAtom3139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08778
  ] at hbad
  tauto

theorem fin15Anchored_clause21645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3139 chi ∧
      ¬Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1423 Fin15AnchoredAtom3139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08778
  ] at hbad
  tauto

theorem fin15Anchored_clause21646 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3139 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1038 chi ∧
      Fin15AnchoredAtom1423 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom0911 Fin15AnchoredAtom0929
    Fin15AnchoredAtom1038 Fin15AnchoredAtom1423 Fin15AnchoredAtom3139 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08778
  ] at hbad
  tauto

theorem fin15Anchored_clause21647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom3140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16970
  ] at hbad
  tauto

theorem fin15Anchored_clause21648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom3140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16970
  ] at hbad
  tauto

theorem fin15Anchored_clause21649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom3140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16970
  ] at hbad
  tauto

theorem fin15Anchored_clause21650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom1039 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1039 Fin15AnchoredAtom3140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16970
  ] at hbad
  tauto

theorem fin15Anchored_clause21651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3140 chi ∧
      ¬Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1424 Fin15AnchoredAtom3140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16970
  ] at hbad
  tauto

theorem fin15Anchored_clause21652 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3140 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1039 chi ∧
      Fin15AnchoredAtom1424 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom0912 Fin15AnchoredAtom0930
    Fin15AnchoredAtom1039 Fin15AnchoredAtom1424 Fin15AnchoredAtom3140 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16970
  ] at hbad
  tauto

theorem fin15Anchored_clause21653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3141 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom3141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03146
  ] at hbad
  tauto

theorem fin15Anchored_clause21654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3141 chi ∧
      ¬Fin15AnchoredAtom0909 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0909 Fin15AnchoredAtom3141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03146
  ] at hbad
  tauto

theorem fin15Anchored_clause21655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3141 chi ∧
      ¬Fin15AnchoredAtom1425 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1425 Fin15AnchoredAtom3141 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03146
  ] at hbad
  tauto

theorem fin15Anchored_clause21656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom3142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05194
  ] at hbad
  tauto

theorem fin15Anchored_clause21657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom3142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05194
  ] at hbad
  tauto

theorem fin15Anchored_clause21658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom3142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05194
  ] at hbad
  tauto

theorem fin15Anchored_clause21659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom1041 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1041 Fin15AnchoredAtom3142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05194
  ] at hbad
  tauto

theorem fin15Anchored_clause21660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3142 chi ∧
      ¬Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1426 Fin15AnchoredAtom3142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05194
  ] at hbad
  tauto

theorem fin15Anchored_clause21661 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3142 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1041 chi ∧
      Fin15AnchoredAtom1426 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom0910 Fin15AnchoredAtom0932
    Fin15AnchoredAtom1041 Fin15AnchoredAtom1426 Fin15AnchoredAtom3142 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05194
  ] at hbad
  tauto

theorem fin15Anchored_clause21662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom3143 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09290
  ] at hbad
  tauto

theorem fin15Anchored_clause21663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom3143 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09290
  ] at hbad
  tauto

theorem fin15Anchored_clause21664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom3143 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09290
  ] at hbad
  tauto

theorem fin15Anchored_clause21665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom1042 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1042 Fin15AnchoredAtom3143 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09290
  ] at hbad
  tauto

theorem fin15Anchored_clause21666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3143 chi ∧
      ¬Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1427 Fin15AnchoredAtom3143 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09290
  ] at hbad
  tauto

theorem fin15Anchored_clause21667 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3143 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1042 chi ∧
      Fin15AnchoredAtom1427 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom0911 Fin15AnchoredAtom0933
    Fin15AnchoredAtom1042 Fin15AnchoredAtom1427 Fin15AnchoredAtom3143 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09290
  ] at hbad
  tauto

theorem fin15Anchored_clause21668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom3144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17482
  ] at hbad
  tauto

theorem fin15Anchored_clause21669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom3144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17482
  ] at hbad
  tauto

theorem fin15Anchored_clause21670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom3144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17482
  ] at hbad
  tauto

theorem fin15Anchored_clause21671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom1043 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1043 Fin15AnchoredAtom3144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17482
  ] at hbad
  tauto

theorem fin15Anchored_clause21672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3144 chi ∧
      ¬Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1428 Fin15AnchoredAtom3144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17482
  ] at hbad
  tauto

theorem fin15Anchored_clause21673 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3144 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1043 chi ∧
      Fin15AnchoredAtom1428 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom0912 Fin15AnchoredAtom0934
    Fin15AnchoredAtom1043 Fin15AnchoredAtom1428 Fin15AnchoredAtom3144 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17482
  ] at hbad
  tauto

theorem fin15Anchored_clause21674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3145 chi ∧
      ¬Fin15AnchoredAtom1044 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1044 Fin15AnchoredAtom3145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06218
  ] at hbad
  tauto

theorem fin15Anchored_clause21675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3145 chi ∧
      ¬Fin15AnchoredAtom1429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1429 Fin15AnchoredAtom3145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06218
  ] at hbad
  tauto

theorem fin15Anchored_clause21676 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3145 chi ∧
      Fin15AnchoredAtom0909 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0935 chi ∧
      Fin15AnchoredAtom1044 chi ∧
      Fin15AnchoredAtom1429 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0909 Fin15AnchoredAtom0910 Fin15AnchoredAtom0935
    Fin15AnchoredAtom1044 Fin15AnchoredAtom1429 Fin15AnchoredAtom3145 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06218
  ] at hbad
  tauto

theorem fin15Anchored_clause21677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom3148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12362
  ] at hbad
  tauto

theorem fin15Anchored_clause21678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom3148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12362
  ] at hbad
  tauto

theorem fin15Anchored_clause21679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom3148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12362
  ] at hbad
  tauto

theorem fin15Anchored_clause21680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom1047 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1047 Fin15AnchoredAtom3148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12362
  ] at hbad
  tauto

theorem fin15Anchored_clause21681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3148 chi ∧
      ¬Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1432 Fin15AnchoredAtom3148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12362
  ] at hbad
  tauto

theorem fin15Anchored_clause21682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3148 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1047 chi ∧
      Fin15AnchoredAtom1432 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom0911 Fin15AnchoredAtom0938
    Fin15AnchoredAtom1047 Fin15AnchoredAtom1432 Fin15AnchoredAtom3148 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12362
  ] at hbad
  tauto

theorem fin15Anchored_clause21683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom3149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20554
  ] at hbad
  tauto

theorem fin15Anchored_clause21684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom3149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20554
  ] at hbad
  tauto

theorem fin15Anchored_clause21685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom3149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20554
  ] at hbad
  tauto

theorem fin15Anchored_clause21686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom1048 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1048 Fin15AnchoredAtom3149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20554
  ] at hbad
  tauto

theorem fin15Anchored_clause21687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3149 chi ∧
      ¬Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1433 Fin15AnchoredAtom3149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20554
  ] at hbad
  tauto

theorem fin15Anchored_clause21688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3149 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1048 chi ∧
      Fin15AnchoredAtom1433 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom0912 Fin15AnchoredAtom0939
    Fin15AnchoredAtom1048 Fin15AnchoredAtom1433 Fin15AnchoredAtom3149 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20554
  ] at hbad
  tauto

theorem fin15Anchored_clause21689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom3150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24650
  ] at hbad
  tauto

theorem fin15Anchored_clause21690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom3150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24650
  ] at hbad
  tauto

theorem fin15Anchored_clause21691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom3150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24650
  ] at hbad
  tauto

theorem fin15Anchored_clause21692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom1049 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1049 Fin15AnchoredAtom3150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24650
  ] at hbad
  tauto

theorem fin15Anchored_clause21693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3150 chi ∧
      ¬Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1434 Fin15AnchoredAtom3150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24650
  ] at hbad
  tauto

theorem fin15Anchored_clause21694 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3150 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1049 chi ∧
      Fin15AnchoredAtom1434 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom0912 Fin15AnchoredAtom0940
    Fin15AnchoredAtom1049 Fin15AnchoredAtom1434 Fin15AnchoredAtom3150 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24650
  ] at hbad
  tauto

theorem fin15Anchored_clause21695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom3151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00906
  ] at hbad
  tauto

theorem fin15Anchored_clause21696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom3151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00906
  ] at hbad
  tauto

theorem fin15Anchored_clause21697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom0920 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0920 Fin15AnchoredAtom3151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00906
  ] at hbad
  tauto

theorem fin15Anchored_clause21698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom1050 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1050 Fin15AnchoredAtom3151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00906
  ] at hbad
  tauto

theorem fin15Anchored_clause21699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3151 chi ∧
      ¬Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1435 Fin15AnchoredAtom3151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00906
  ] at hbad
  tauto

theorem fin15Anchored_clause21700 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3151 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0920 chi ∧
      Fin15AnchoredAtom1050 chi ∧
      Fin15AnchoredAtom1435 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom0914 Fin15AnchoredAtom0920
    Fin15AnchoredAtom1050 Fin15AnchoredAtom1435 Fin15AnchoredAtom3151 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00906
  ] at hbad
  tauto

theorem fin15Anchored_clause21701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom3152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01418
  ] at hbad
  tauto

theorem fin15Anchored_clause21702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom3152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01418
  ] at hbad
  tauto

theorem fin15Anchored_clause21703 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom1051 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1051 Fin15AnchoredAtom3152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01418
  ] at hbad
  tauto

theorem fin15Anchored_clause21704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3152 chi ∧
      ¬Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1436 Fin15AnchoredAtom3152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01418
  ] at hbad
  tauto

theorem fin15Anchored_clause21705 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3152 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom1051 chi ∧
      Fin15AnchoredAtom1436 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom0915 Fin15AnchoredAtom0921
    Fin15AnchoredAtom1051 Fin15AnchoredAtom1436 Fin15AnchoredAtom3152 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01418
  ] at hbad
  tauto

theorem fin15Anchored_clause21706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom3154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04490
  ] at hbad
  tauto

theorem fin15Anchored_clause21707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom3154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04490
  ] at hbad
  tauto

theorem fin15Anchored_clause21708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom1053 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1053 Fin15AnchoredAtom3154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04490
  ] at hbad
  tauto

theorem fin15Anchored_clause21709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3154 chi ∧
      ¬Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1438 Fin15AnchoredAtom3154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04490
  ] at hbad
  tauto

theorem fin15Anchored_clause21710 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3154 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom1053 chi ∧
      Fin15AnchoredAtom1438 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom0917 Fin15AnchoredAtom0923
    Fin15AnchoredAtom1053 Fin15AnchoredAtom1438 Fin15AnchoredAtom3154 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04490
  ] at hbad
  tauto

theorem fin15Anchored_clause21711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom3155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08586
  ] at hbad
  tauto

theorem fin15Anchored_clause21712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom3155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08586
  ] at hbad
  tauto

theorem fin15Anchored_clause21713 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom0924 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0924 Fin15AnchoredAtom3155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08586
  ] at hbad
  tauto

theorem fin15Anchored_clause21714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom1054 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1054 Fin15AnchoredAtom3155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08586
  ] at hbad
  tauto

theorem fin15Anchored_clause21715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3155 chi ∧
      ¬Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1439 Fin15AnchoredAtom3155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08586
  ] at hbad
  tauto

theorem fin15Anchored_clause21716 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3155 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0924 chi ∧
      Fin15AnchoredAtom1054 chi ∧
      Fin15AnchoredAtom1439 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom0918 Fin15AnchoredAtom0924
    Fin15AnchoredAtom1054 Fin15AnchoredAtom1439 Fin15AnchoredAtom3155 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08586
  ] at hbad
  tauto

theorem fin15Anchored_clause21717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom0913 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom3156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16778
  ] at hbad
  tauto

theorem fin15Anchored_clause21718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom3156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16778
  ] at hbad
  tauto

theorem fin15Anchored_clause21719 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom1055 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1055 Fin15AnchoredAtom3156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16778
  ] at hbad
  tauto

theorem fin15Anchored_clause21720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3156 chi ∧
      ¬Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1440 Fin15AnchoredAtom3156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16778
  ] at hbad
  tauto

theorem fin15Anchored_clause21721 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3156 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0925 chi ∧
      Fin15AnchoredAtom1055 chi ∧
      Fin15AnchoredAtom1440 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0913 Fin15AnchoredAtom0919 Fin15AnchoredAtom0925
    Fin15AnchoredAtom1055 Fin15AnchoredAtom1440 Fin15AnchoredAtom3156 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16778
  ] at hbad
  tauto

theorem fin15Anchored_clause21722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom3157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01674
  ] at hbad
  tauto

theorem fin15Anchored_clause21723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom3157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01674
  ] at hbad
  tauto

theorem fin15Anchored_clause21724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom3157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01674
  ] at hbad
  tauto

theorem fin15Anchored_clause21725 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom1056 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1056 Fin15AnchoredAtom3157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01674
  ] at hbad
  tauto

theorem fin15Anchored_clause21726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3157 chi ∧
      ¬Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1441 Fin15AnchoredAtom3157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01674
  ] at hbad
  tauto

theorem fin15Anchored_clause21727 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3157 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1056 chi ∧
      Fin15AnchoredAtom1441 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom0915 Fin15AnchoredAtom0926
    Fin15AnchoredAtom1056 Fin15AnchoredAtom1441 Fin15AnchoredAtom3157 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01674
  ] at hbad
  tauto

theorem fin15Anchored_clause21728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom3158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02698
  ] at hbad
  tauto

theorem fin15Anchored_clause21729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom0927 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0927 Fin15AnchoredAtom3158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02698
  ] at hbad
  tauto

theorem fin15Anchored_clause21730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3158 chi ∧
      ¬Fin15AnchoredAtom1442 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1442 Fin15AnchoredAtom3158 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02698
  ] at hbad
  tauto

theorem fin15Anchored_clause21731 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom3159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04746
  ] at hbad
  tauto

theorem fin15Anchored_clause21732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom3159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04746
  ] at hbad
  tauto

theorem fin15Anchored_clause21733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom3159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04746
  ] at hbad
  tauto

theorem fin15Anchored_clause21734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom1058 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1058 Fin15AnchoredAtom3159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04746
  ] at hbad
  tauto

theorem fin15Anchored_clause21735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3159 chi ∧
      ¬Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1443 Fin15AnchoredAtom3159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04746
  ] at hbad
  tauto

theorem fin15Anchored_clause21736 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3159 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1058 chi ∧
      Fin15AnchoredAtom1443 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom0917 Fin15AnchoredAtom0928
    Fin15AnchoredAtom1058 Fin15AnchoredAtom1443 Fin15AnchoredAtom3159 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04746
  ] at hbad
  tauto

theorem fin15Anchored_clause21737 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom3160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08842
  ] at hbad
  tauto

theorem fin15Anchored_clause21738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom3160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08842
  ] at hbad
  tauto

theorem fin15Anchored_clause21739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom3160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08842
  ] at hbad
  tauto

theorem fin15Anchored_clause21740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom1059 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1059 Fin15AnchoredAtom3160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08842
  ] at hbad
  tauto

theorem fin15Anchored_clause21741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3160 chi ∧
      ¬Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1444 Fin15AnchoredAtom3160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08842
  ] at hbad
  tauto

theorem fin15Anchored_clause21742 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3160 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1059 chi ∧
      Fin15AnchoredAtom1444 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom0918 Fin15AnchoredAtom0929
    Fin15AnchoredAtom1059 Fin15AnchoredAtom1444 Fin15AnchoredAtom3160 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08842
  ] at hbad
  tauto

theorem fin15Anchored_clause21743 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom3161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17034
  ] at hbad
  tauto

theorem fin15Anchored_clause21744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom3161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17034
  ] at hbad
  tauto

theorem fin15Anchored_clause21745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom3161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17034
  ] at hbad
  tauto

theorem fin15Anchored_clause21746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom1060 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1060 Fin15AnchoredAtom3161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17034
  ] at hbad
  tauto

theorem fin15Anchored_clause21747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3161 chi ∧
      ¬Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1445 Fin15AnchoredAtom3161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17034
  ] at hbad
  tauto

theorem fin15Anchored_clause21748 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3161 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1060 chi ∧
      Fin15AnchoredAtom1445 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom0919 Fin15AnchoredAtom0930
    Fin15AnchoredAtom1060 Fin15AnchoredAtom1445 Fin15AnchoredAtom3161 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17034
  ] at hbad
  tauto

theorem fin15Anchored_clause21749 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom3162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03210
  ] at hbad
  tauto

theorem fin15Anchored_clause21750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom0916 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0916 Fin15AnchoredAtom3162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03210
  ] at hbad
  tauto

theorem fin15Anchored_clause21751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3162 chi ∧
      ¬Fin15AnchoredAtom1061 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1061 Fin15AnchoredAtom3162 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03210
  ] at hbad
  tauto

theorem fin15Anchored_clause21752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom3163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05258
  ] at hbad
  tauto

theorem fin15Anchored_clause21753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom3163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05258
  ] at hbad
  tauto

theorem fin15Anchored_clause21754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom3163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05258
  ] at hbad
  tauto

theorem fin15Anchored_clause21755 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom3163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05258
  ] at hbad
  tauto

theorem fin15Anchored_clause21756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3163 chi ∧
      ¬Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1447 Fin15AnchoredAtom3163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05258
  ] at hbad
  tauto

theorem fin15Anchored_clause21757 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3163 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1447 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom0917 Fin15AnchoredAtom0932
    Fin15AnchoredAtom1062 Fin15AnchoredAtom1447 Fin15AnchoredAtom3163 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05258
  ] at hbad
  tauto

theorem fin15Anchored_clause21758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom3164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09354
  ] at hbad
  tauto

theorem fin15Anchored_clause21759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3164 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom3164 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09354
  ] at hbad
  tauto

end ErdosSzekeres

end
