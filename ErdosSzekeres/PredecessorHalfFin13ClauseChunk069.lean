module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 069. -/

theorem predecessorHalfFin13_clause19711 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom1427 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0481
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19712 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom1427 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0481
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19713 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom1427 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0481
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19714 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom1427 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0481
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19715 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1427 chi ∧
      ¬PredecessorHalfFin13Atom0932 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0932 PredecessorHalfFin13Atom1427 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0481
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19717 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom1428 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0737
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19718 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom1428 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0737
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19719 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom1428 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0737
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19720 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom1428 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0737
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19721 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1428 chi ∧
      ¬PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom1428 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0737
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19722 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1428 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0933 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0458
    PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0933 PredecessorHalfFin13Atom1428 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0737
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19723 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom1429 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19724 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom1429 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19725 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom1429 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19726 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom1429 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19727 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1429 chi ∧
      ¬PredecessorHalfFin13Atom0934 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0934 PredecessorHalfFin13Atom1429 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1249
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19735 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0451 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom1431 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19736 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom1431 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19737 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom1431 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19738 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom1431 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19739 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1431 chi ∧
      ¬PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom1431 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19740 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1431 chi ∧
      PredecessorHalfFin13Atom0451 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0476 chi ∧
      PredecessorHalfFin13Atom0936 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0451 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0461
    PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom0936 PredecessorHalfFin13Atom1431 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4321
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19741 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom1432 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0865
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19742 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom1432 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0865
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19743 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom1432 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0865
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19744 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom1432 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0865
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19745 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1432 chi ∧
      ¬PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom1432 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0865
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19746 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1432 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0937 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0462
    PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom0937 PredecessorHalfFin13Atom1432 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0865
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19747 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom1433 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19748 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom1433 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19749 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom1433 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19750 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom1433 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19751 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1433 chi ∧
      ¬PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom1433 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19752 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1433 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0454 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0938 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom0463
    PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom0938 PredecessorHalfFin13Atom1433 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1377
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19759 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0452 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom1435 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4449
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19760 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom1435 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4449
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19761 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom1435 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4449
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19762 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0480 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom1435 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4449
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19763 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1435 chi ∧
      ¬PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom1435 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4449
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19764 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1435 chi ∧
      PredecessorHalfFin13Atom0452 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0480 chi ∧
      PredecessorHalfFin13Atom0940 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0452 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0465
    PredecessorHalfFin13Atom0480 PredecessorHalfFin13Atom0940 PredecessorHalfFin13Atom1435 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4449
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19765 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom1436 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19766 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom1436 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19767 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom1436 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19768 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0481 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0481 PredecessorHalfFin13Atom1436 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19769 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1436 chi ∧
      ¬PredecessorHalfFin13Atom0941 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0941 PredecessorHalfFin13Atom1436 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1633
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19777 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0453 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom1438 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4705
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19778 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom1438 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4705
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19779 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom1438 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4705
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19780 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0483 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom1438 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4705
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19781 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1438 chi ∧
      ¬PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom1438 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4705
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19782 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1438 chi ∧
      PredecessorHalfFin13Atom0453 chi ∧
      PredecessorHalfFin13Atom0456 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0483 chi ∧
      PredecessorHalfFin13Atom0943 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0453 PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0483 PredecessorHalfFin13Atom0943 PredecessorHalfFin13Atom1438 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4705
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19789 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0454 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0454 PredecessorHalfFin13Atom1440 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19790 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0456 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0456 PredecessorHalfFin13Atom1440 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19791 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom1440 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19792 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0485 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0485 PredecessorHalfFin13Atom1440 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19793 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1440 chi ∧
      ¬PredecessorHalfFin13Atom0945 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0945 PredecessorHalfFin13Atom1440 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5217
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19801 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom1442 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19802 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom1442 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19803 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom1442 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19804 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom1442 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19805 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1442 chi ∧
      ¬PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom1442 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19806 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1442 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0947 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0462
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0947 PredecessorHalfFin13Atom1442 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0929
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19807 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom1443 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19808 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom1443 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19809 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom1443 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19810 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom1443 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19811 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1443 chi ∧
      ¬PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom1443 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19812 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1443 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0948 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0463
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0948 PredecessorHalfFin13Atom1443 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1441
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19819 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0457 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom1445 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4513
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19820 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom1445 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4513
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19821 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom1445 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4513
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19822 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0490 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom1445 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4513
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19823 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1445 chi ∧
      ¬PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom1445 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4513
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19824 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1445 chi ∧
      PredecessorHalfFin13Atom0457 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0490 chi ∧
      PredecessorHalfFin13Atom0950 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0457 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0465
    PredecessorHalfFin13Atom0490 PredecessorHalfFin13Atom0950 PredecessorHalfFin13Atom1445 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4513
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19825 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom1446 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19826 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom1446 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19827 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom1446 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19828 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0491 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom1446 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19829 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1446 chi ∧
      ¬PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom1446 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19830 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1446 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0491 chi ∧
      PredecessorHalfFin13Atom0951 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom0466
    PredecessorHalfFin13Atom0491 PredecessorHalfFin13Atom0951 PredecessorHalfFin13Atom1446 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1697
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19837 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0458 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom1448 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4769
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19838 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom1448 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4769
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19839 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom1448 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4769
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19840 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0493 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom1448 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4769
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19841 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1448 chi ∧
      ¬PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom1448 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4769
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19842 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1448 chi ∧
      PredecessorHalfFin13Atom0458 chi ∧
      PredecessorHalfFin13Atom0461 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0493 chi ∧
      PredecessorHalfFin13Atom0953 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0458 PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0493 PredecessorHalfFin13Atom0953 PredecessorHalfFin13Atom1448 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4769
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19849 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0459 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0459 PredecessorHalfFin13Atom1450 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5281
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19850 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0461 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0461 PredecessorHalfFin13Atom1450 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5281
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19851 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom1450 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5281
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19852 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0495 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0495 PredecessorHalfFin13Atom1450 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5281
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19853 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1450 chi ∧
      ¬PredecessorHalfFin13Atom0955 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0955 PredecessorHalfFin13Atom1450 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5281
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19861 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom1452 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1825
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19862 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom1452 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1825
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19863 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom1452 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1825
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19864 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0497 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0497 PredecessorHalfFin13Atom1452 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1825
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19865 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1452 chi ∧
      ¬PredecessorHalfFin13Atom0957 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0957 PredecessorHalfFin13Atom1452 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1825
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19873 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0462 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom1454 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4897
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19874 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom1454 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4897
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19875 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom1454 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4897
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19876 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0499 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom1454 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4897
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19877 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1454 chi ∧
      ¬PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom1454 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4897
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19878 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1454 chi ∧
      PredecessorHalfFin13Atom0462 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0499 chi ∧
      PredecessorHalfFin13Atom0959 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0462 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0468
    PredecessorHalfFin13Atom0499 PredecessorHalfFin13Atom0959 PredecessorHalfFin13Atom1454 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4897
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19885 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0463 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom1456 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19886 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0465 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom1456 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19887 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom1456 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19888 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0501 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom1456 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19889 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1456 chi ∧
      ¬PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom1456 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19890 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1456 chi ∧
      PredecessorHalfFin13Atom0463 chi ∧
      PredecessorHalfFin13Atom0465 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0501 chi ∧
      PredecessorHalfFin13Atom0961 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0463 PredecessorHalfFin13Atom0465 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0501 PredecessorHalfFin13Atom0961 PredecessorHalfFin13Atom1456 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5409
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19903 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0466 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom1459 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19904 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0468 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom1459 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19905 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0470 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0470 PredecessorHalfFin13Atom1459 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19906 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0504 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom1459 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19907 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1459 chi ∧
      ¬PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom1459 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19908 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1459 chi ∧
      PredecessorHalfFin13Atom0466 chi ∧
      PredecessorHalfFin13Atom0468 chi ∧
      PredecessorHalfFin13Atom0470 chi ∧
      PredecessorHalfFin13Atom0504 chi ∧
      PredecessorHalfFin13Atom0964 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0466 PredecessorHalfFin13Atom0468 PredecessorHalfFin13Atom0470
    PredecessorHalfFin13Atom0504 PredecessorHalfFin13Atom0964 PredecessorHalfFin13Atom1459 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5665
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19921 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom1462 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0961
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19922 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0473 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom1462 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0961
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19923 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0477 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0477 PredecessorHalfFin13Atom1462 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0961
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19924 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0487 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom1462 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0961
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19925 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1462 chi ∧
      ¬PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom1462 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0961
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19926 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1462 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0473 chi ∧
      PredecessorHalfFin13Atom0477 chi ∧
      PredecessorHalfFin13Atom0487 chi ∧
      PredecessorHalfFin13Atom0967 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0473 PredecessorHalfFin13Atom0477
    PredecessorHalfFin13Atom0487 PredecessorHalfFin13Atom0967 PredecessorHalfFin13Atom1462 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0961
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19927 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom1463 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1473
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19928 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0474 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom1463 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1473
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19929 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0478 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0478 PredecessorHalfFin13Atom1463 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1473
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19930 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0488 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom1463 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1473
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19931 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1463 chi ∧
      ¬PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom1463 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1473
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19932 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1463 chi ∧
      PredecessorHalfFin13Atom0472 chi ∧
      PredecessorHalfFin13Atom0474 chi ∧
      PredecessorHalfFin13Atom0478 chi ∧
      PredecessorHalfFin13Atom0488 chi ∧
      PredecessorHalfFin13Atom0968 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom0474 PredecessorHalfFin13Atom0478
    PredecessorHalfFin13Atom0488 PredecessorHalfFin13Atom0968 PredecessorHalfFin13Atom1463 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1473
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19939 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0472 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0472 PredecessorHalfFin13Atom1465 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4545
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause19940 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1465 chi ∧
      ¬PredecessorHalfFin13Atom0476 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0476 PredecessorHalfFin13Atom1465 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4545
  ] at hbad
  tauto

end ErdosSzekeres

end
