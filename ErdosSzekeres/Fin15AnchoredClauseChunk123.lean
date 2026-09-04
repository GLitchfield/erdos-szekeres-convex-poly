module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 123. -/

theorem fin15Anchored_clause15744 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00283
  ] at hbad
  tauto

theorem fin15Anchored_clause15745 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00283
  ] at hbad
  tauto

theorem fin15Anchored_clause15746 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00283
  ] at hbad
  tauto

theorem fin15Anchored_clause15747 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0603 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0603 Fin15AnchoredAtom1890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00283
  ] at hbad
  tauto

theorem fin15Anchored_clause15748 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1890 chi ∧
      ¬Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0889 Fin15AnchoredAtom1890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00283
  ] at hbad
  tauto

theorem fin15Anchored_clause15749 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1890 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0603 chi ∧
      Fin15AnchoredAtom0889 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0472 Fin15AnchoredAtom0482
    Fin15AnchoredAtom0603 Fin15AnchoredAtom0889 Fin15AnchoredAtom1890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00283
  ] at hbad
  tauto

theorem fin15Anchored_clause15750 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00539
  ] at hbad
  tauto

theorem fin15Anchored_clause15751 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00539
  ] at hbad
  tauto

theorem fin15Anchored_clause15752 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00539
  ] at hbad
  tauto

theorem fin15Anchored_clause15753 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0604 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0604 Fin15AnchoredAtom1891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00539
  ] at hbad
  tauto

theorem fin15Anchored_clause15754 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1891 chi ∧
      ¬Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0890 Fin15AnchoredAtom1891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00539
  ] at hbad
  tauto

theorem fin15Anchored_clause15755 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1891 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0604 chi ∧
      Fin15AnchoredAtom0890 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0473 Fin15AnchoredAtom0483
    Fin15AnchoredAtom0604 Fin15AnchoredAtom0890 Fin15AnchoredAtom1891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00539
  ] at hbad
  tauto

theorem fin15Anchored_clause15756 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01051
  ] at hbad
  tauto

theorem fin15Anchored_clause15757 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01051
  ] at hbad
  tauto

theorem fin15Anchored_clause15758 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01051
  ] at hbad
  tauto

theorem fin15Anchored_clause15759 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0605 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0605 Fin15AnchoredAtom1892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01051
  ] at hbad
  tauto

theorem fin15Anchored_clause15760 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1892 chi ∧
      ¬Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0891 Fin15AnchoredAtom1892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01051
  ] at hbad
  tauto

theorem fin15Anchored_clause15761 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1892 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0605 chi ∧
      Fin15AnchoredAtom0891 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0474 Fin15AnchoredAtom0484
    Fin15AnchoredAtom0605 Fin15AnchoredAtom0891 Fin15AnchoredAtom1892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01051
  ] at hbad
  tauto

theorem fin15Anchored_clause15762 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02075
  ] at hbad
  tauto

theorem fin15Anchored_clause15763 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0475 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0475 Fin15AnchoredAtom1893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02075
  ] at hbad
  tauto

theorem fin15Anchored_clause15764 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0485 Fin15AnchoredAtom1893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02075
  ] at hbad
  tauto

theorem fin15Anchored_clause15765 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0606 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0606 Fin15AnchoredAtom1893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02075
  ] at hbad
  tauto

theorem fin15Anchored_clause15766 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1893 chi ∧
      ¬Fin15AnchoredAtom0892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0892 Fin15AnchoredAtom1893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02075
  ] at hbad
  tauto

theorem fin15Anchored_clause15767 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1893 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0485 chi ∧
      Fin15AnchoredAtom0606 chi ∧
      Fin15AnchoredAtom0892 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0475 Fin15AnchoredAtom0485
    Fin15AnchoredAtom0606 Fin15AnchoredAtom0892 Fin15AnchoredAtom1893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02075
  ] at hbad
  tauto

theorem fin15Anchored_clause15768 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04123
  ] at hbad
  tauto

theorem fin15Anchored_clause15769 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04123
  ] at hbad
  tauto

theorem fin15Anchored_clause15770 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04123
  ] at hbad
  tauto

theorem fin15Anchored_clause15771 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0607 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0607 Fin15AnchoredAtom1894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04123
  ] at hbad
  tauto

theorem fin15Anchored_clause15772 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1894 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom1894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04123
  ] at hbad
  tauto

theorem fin15Anchored_clause15773 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1894 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0607 chi ∧
      Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0476 Fin15AnchoredAtom0486
    Fin15AnchoredAtom0607 Fin15AnchoredAtom0893 Fin15AnchoredAtom1894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04123
  ] at hbad
  tauto

theorem fin15Anchored_clause15774 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08219
  ] at hbad
  tauto

theorem fin15Anchored_clause15775 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08219
  ] at hbad
  tauto

theorem fin15Anchored_clause15776 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08219
  ] at hbad
  tauto

theorem fin15Anchored_clause15777 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0608 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0608 Fin15AnchoredAtom1895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08219
  ] at hbad
  tauto

theorem fin15Anchored_clause15778 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1895 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom1895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08219
  ] at hbad
  tauto

theorem fin15Anchored_clause15779 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1895 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0608 chi ∧
      Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0477 Fin15AnchoredAtom0487
    Fin15AnchoredAtom0608 Fin15AnchoredAtom0894 Fin15AnchoredAtom1895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08219
  ] at hbad
  tauto

theorem fin15Anchored_clause15780 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16411
  ] at hbad
  tauto

theorem fin15Anchored_clause15781 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16411
  ] at hbad
  tauto

theorem fin15Anchored_clause15782 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16411
  ] at hbad
  tauto

theorem fin15Anchored_clause15783 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0609 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0609 Fin15AnchoredAtom1896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16411
  ] at hbad
  tauto

theorem fin15Anchored_clause15784 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1896 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom1896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16411
  ] at hbad
  tauto

theorem fin15Anchored_clause15785 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1896 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0609 chi ∧
      Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0478 Fin15AnchoredAtom0488
    Fin15AnchoredAtom0609 Fin15AnchoredAtom0895 Fin15AnchoredAtom1896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16411
  ] at hbad
  tauto

theorem fin15Anchored_clause15786 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00107
  ] at hbad
  tauto

theorem fin15Anchored_clause15787 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00107
  ] at hbad
  tauto

theorem fin15Anchored_clause15788 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0489 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0489 Fin15AnchoredAtom1897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00107
  ] at hbad
  tauto

theorem fin15Anchored_clause15789 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0610 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0610 Fin15AnchoredAtom1897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00107
  ] at hbad
  tauto

theorem fin15Anchored_clause15790 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1897 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom1897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00107
  ] at hbad
  tauto

theorem fin15Anchored_clause15791 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1897 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0489 chi ∧
      Fin15AnchoredAtom0610 chi ∧
      Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom0470 Fin15AnchoredAtom0489
    Fin15AnchoredAtom0610 Fin15AnchoredAtom0896 Fin15AnchoredAtom1897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00107
  ] at hbad
  tauto

theorem fin15Anchored_clause15792 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00171
  ] at hbad
  tauto

theorem fin15Anchored_clause15793 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00171
  ] at hbad
  tauto

theorem fin15Anchored_clause15794 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0490 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0490 Fin15AnchoredAtom1898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00171
  ] at hbad
  tauto

theorem fin15Anchored_clause15795 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0611 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0611 Fin15AnchoredAtom1898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00171
  ] at hbad
  tauto

theorem fin15Anchored_clause15796 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1898 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom1898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00171
  ] at hbad
  tauto

theorem fin15Anchored_clause15797 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1898 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0490 chi ∧
      Fin15AnchoredAtom0611 chi ∧
      Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom0471 Fin15AnchoredAtom0490
    Fin15AnchoredAtom0611 Fin15AnchoredAtom0897 Fin15AnchoredAtom1898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00171
  ] at hbad
  tauto

theorem fin15Anchored_clause15798 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00299
  ] at hbad
  tauto

theorem fin15Anchored_clause15799 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00299
  ] at hbad
  tauto

theorem fin15Anchored_clause15800 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0491 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0491 Fin15AnchoredAtom1899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00299
  ] at hbad
  tauto

theorem fin15Anchored_clause15801 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0612 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0612 Fin15AnchoredAtom1899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00299
  ] at hbad
  tauto

theorem fin15Anchored_clause15802 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1899 chi ∧
      ¬Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0898 Fin15AnchoredAtom1899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00299
  ] at hbad
  tauto

theorem fin15Anchored_clause15803 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1899 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0491 chi ∧
      Fin15AnchoredAtom0612 chi ∧
      Fin15AnchoredAtom0898 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom0472 Fin15AnchoredAtom0491
    Fin15AnchoredAtom0612 Fin15AnchoredAtom0898 Fin15AnchoredAtom1899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00299
  ] at hbad
  tauto

theorem fin15Anchored_clause15804 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00555
  ] at hbad
  tauto

theorem fin15Anchored_clause15805 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00555
  ] at hbad
  tauto

theorem fin15Anchored_clause15806 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0492 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0492 Fin15AnchoredAtom1900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00555
  ] at hbad
  tauto

theorem fin15Anchored_clause15807 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0613 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0613 Fin15AnchoredAtom1900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00555
  ] at hbad
  tauto

theorem fin15Anchored_clause15808 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1900 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom1900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00555
  ] at hbad
  tauto

theorem fin15Anchored_clause15809 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1900 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0492 chi ∧
      Fin15AnchoredAtom0613 chi ∧
      Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom0473 Fin15AnchoredAtom0492
    Fin15AnchoredAtom0613 Fin15AnchoredAtom0899 Fin15AnchoredAtom1900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00555
  ] at hbad
  tauto

theorem fin15Anchored_clause15810 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01067
  ] at hbad
  tauto

theorem fin15Anchored_clause15811 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01067
  ] at hbad
  tauto

theorem fin15Anchored_clause15812 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0493 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0493 Fin15AnchoredAtom1901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01067
  ] at hbad
  tauto

theorem fin15Anchored_clause15813 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0614 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0614 Fin15AnchoredAtom1901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01067
  ] at hbad
  tauto

theorem fin15Anchored_clause15814 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1901 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom1901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01067
  ] at hbad
  tauto

theorem fin15Anchored_clause15815 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1901 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0493 chi ∧
      Fin15AnchoredAtom0614 chi ∧
      Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom0474 Fin15AnchoredAtom0493
    Fin15AnchoredAtom0614 Fin15AnchoredAtom0900 Fin15AnchoredAtom1901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01067
  ] at hbad
  tauto

theorem fin15Anchored_clause15816 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1902 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1902 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02091
  ] at hbad
  tauto

theorem fin15Anchored_clause15817 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1902 chi ∧
      ¬Fin15AnchoredAtom0615 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0615 Fin15AnchoredAtom1902 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02091
  ] at hbad
  tauto

theorem fin15Anchored_clause15818 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1902 chi ∧
      ¬Fin15AnchoredAtom0901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0901 Fin15AnchoredAtom1902 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02091
  ] at hbad
  tauto

theorem fin15Anchored_clause15819 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1902 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0475 chi ∧
      Fin15AnchoredAtom0494 chi ∧
      Fin15AnchoredAtom0615 chi ∧
      Fin15AnchoredAtom0901 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom0475 Fin15AnchoredAtom0494
    Fin15AnchoredAtom0615 Fin15AnchoredAtom0901 Fin15AnchoredAtom1902 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02091
  ] at hbad
  tauto

theorem fin15Anchored_clause15820 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1903 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04139
  ] at hbad
  tauto

theorem fin15Anchored_clause15821 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1903 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04139
  ] at hbad
  tauto

theorem fin15Anchored_clause15822 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0495 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0495 Fin15AnchoredAtom1903 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04139
  ] at hbad
  tauto

theorem fin15Anchored_clause15823 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0616 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0616 Fin15AnchoredAtom1903 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04139
  ] at hbad
  tauto

theorem fin15Anchored_clause15824 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1903 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom1903 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04139
  ] at hbad
  tauto

theorem fin15Anchored_clause15825 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1903 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0495 chi ∧
      Fin15AnchoredAtom0616 chi ∧
      Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom0476 Fin15AnchoredAtom0495
    Fin15AnchoredAtom0616 Fin15AnchoredAtom0902 Fin15AnchoredAtom1903 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04139
  ] at hbad
  tauto

theorem fin15Anchored_clause15826 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1904 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08235
  ] at hbad
  tauto

theorem fin15Anchored_clause15827 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1904 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08235
  ] at hbad
  tauto

theorem fin15Anchored_clause15828 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0496 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0496 Fin15AnchoredAtom1904 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08235
  ] at hbad
  tauto

theorem fin15Anchored_clause15829 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0617 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0617 Fin15AnchoredAtom1904 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08235
  ] at hbad
  tauto

theorem fin15Anchored_clause15830 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1904 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom1904 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08235
  ] at hbad
  tauto

theorem fin15Anchored_clause15831 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1904 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0477 chi ∧
      Fin15AnchoredAtom0496 chi ∧
      Fin15AnchoredAtom0617 chi ∧
      Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom0477 Fin15AnchoredAtom0496
    Fin15AnchoredAtom0617 Fin15AnchoredAtom0903 Fin15AnchoredAtom1904 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08235
  ] at hbad
  tauto

theorem fin15Anchored_clause15832 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16427
  ] at hbad
  tauto

theorem fin15Anchored_clause15833 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0478 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0478 Fin15AnchoredAtom1905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16427
  ] at hbad
  tauto

theorem fin15Anchored_clause15834 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0497 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0497 Fin15AnchoredAtom1905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16427
  ] at hbad
  tauto

theorem fin15Anchored_clause15835 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0618 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0618 Fin15AnchoredAtom1905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16427
  ] at hbad
  tauto

theorem fin15Anchored_clause15836 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1905 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom1905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16427
  ] at hbad
  tauto

theorem fin15Anchored_clause15837 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1905 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0478 chi ∧
      Fin15AnchoredAtom0497 chi ∧
      Fin15AnchoredAtom0618 chi ∧
      Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom0478 Fin15AnchoredAtom0497
    Fin15AnchoredAtom0618 Fin15AnchoredAtom0904 Fin15AnchoredAtom1905 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16427
  ] at hbad
  tauto

theorem fin15Anchored_clause15838 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00203
  ] at hbad
  tauto

theorem fin15Anchored_clause15839 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00203
  ] at hbad
  tauto

theorem fin15Anchored_clause15840 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0498 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0498 Fin15AnchoredAtom1906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00203
  ] at hbad
  tauto

theorem fin15Anchored_clause15841 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0619 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0619 Fin15AnchoredAtom1906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00203
  ] at hbad
  tauto

theorem fin15Anchored_clause15842 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1906 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom1906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00203
  ] at hbad
  tauto

theorem fin15Anchored_clause15843 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1906 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0498 chi ∧
      Fin15AnchoredAtom0619 chi ∧
      Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom0471 Fin15AnchoredAtom0498
    Fin15AnchoredAtom0619 Fin15AnchoredAtom0905 Fin15AnchoredAtom1906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00203
  ] at hbad
  tauto

theorem fin15Anchored_clause15844 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00331
  ] at hbad
  tauto

theorem fin15Anchored_clause15845 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom0472 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0472 Fin15AnchoredAtom1907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00331
  ] at hbad
  tauto

theorem fin15Anchored_clause15846 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom0499 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0499 Fin15AnchoredAtom1907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00331
  ] at hbad
  tauto

theorem fin15Anchored_clause15847 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1907 chi ∧
      ¬Fin15AnchoredAtom0620 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0620 Fin15AnchoredAtom1907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00331
  ] at hbad
  tauto

theorem fin15Anchored_clause15848 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1907 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0472 chi ∧
      Fin15AnchoredAtom0499 chi ∧
      Fin15AnchoredAtom0620 chi ∧
      Fin15AnchoredAtom0906 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom0472 Fin15AnchoredAtom0499
    Fin15AnchoredAtom0620 Fin15AnchoredAtom0906 Fin15AnchoredAtom1907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00331
  ] at hbad
  tauto

theorem fin15Anchored_clause15849 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1908 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00587
  ] at hbad
  tauto

theorem fin15Anchored_clause15850 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0473 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0473 Fin15AnchoredAtom1908 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00587
  ] at hbad
  tauto

theorem fin15Anchored_clause15851 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0500 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0500 Fin15AnchoredAtom1908 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00587
  ] at hbad
  tauto

theorem fin15Anchored_clause15852 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0621 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0621 Fin15AnchoredAtom1908 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00587
  ] at hbad
  tauto

theorem fin15Anchored_clause15853 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1908 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom1908 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00587
  ] at hbad
  tauto

theorem fin15Anchored_clause15854 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1908 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0473 chi ∧
      Fin15AnchoredAtom0500 chi ∧
      Fin15AnchoredAtom0621 chi ∧
      Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom0473 Fin15AnchoredAtom0500
    Fin15AnchoredAtom0621 Fin15AnchoredAtom0907 Fin15AnchoredAtom1908 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00587
  ] at hbad
  tauto

theorem fin15Anchored_clause15855 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01099
  ] at hbad
  tauto

theorem fin15Anchored_clause15856 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0474 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0474 Fin15AnchoredAtom1909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01099
  ] at hbad
  tauto

theorem fin15Anchored_clause15857 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0501 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0501 Fin15AnchoredAtom1909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01099
  ] at hbad
  tauto

theorem fin15Anchored_clause15858 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0622 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0622 Fin15AnchoredAtom1909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01099
  ] at hbad
  tauto

theorem fin15Anchored_clause15859 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1909 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom1909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01099
  ] at hbad
  tauto

theorem fin15Anchored_clause15860 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1909 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0474 chi ∧
      Fin15AnchoredAtom0501 chi ∧
      Fin15AnchoredAtom0622 chi ∧
      Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom0474 Fin15AnchoredAtom0501
    Fin15AnchoredAtom0622 Fin15AnchoredAtom0908 Fin15AnchoredAtom1909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01099
  ] at hbad
  tauto

theorem fin15Anchored_clause15861 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1910 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1910 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02123
  ] at hbad
  tauto

theorem fin15Anchored_clause15862 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1910 chi ∧
      ¬Fin15AnchoredAtom0623 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0623 Fin15AnchoredAtom1910 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02123
  ] at hbad
  tauto

theorem fin15Anchored_clause15863 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04171
  ] at hbad
  tauto

theorem fin15Anchored_clause15864 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0476 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0476 Fin15AnchoredAtom1911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04171
  ] at hbad
  tauto

theorem fin15Anchored_clause15865 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0503 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0503 Fin15AnchoredAtom1911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04171
  ] at hbad
  tauto

theorem fin15Anchored_clause15866 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0624 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0624 Fin15AnchoredAtom1911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04171
  ] at hbad
  tauto

theorem fin15Anchored_clause15867 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1911 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom1911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04171
  ] at hbad
  tauto

theorem fin15Anchored_clause15868 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1911 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0476 chi ∧
      Fin15AnchoredAtom0503 chi ∧
      Fin15AnchoredAtom0624 chi ∧
      Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom0476 Fin15AnchoredAtom0503
    Fin15AnchoredAtom0624 Fin15AnchoredAtom0910 Fin15AnchoredAtom1911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04171
  ] at hbad
  tauto

theorem fin15Anchored_clause15869 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08267
  ] at hbad
  tauto

theorem fin15Anchored_clause15870 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0477 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0477 Fin15AnchoredAtom1912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08267
  ] at hbad
  tauto

theorem fin15Anchored_clause15871 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1912 chi ∧
      ¬Fin15AnchoredAtom0504 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0504 Fin15AnchoredAtom1912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08267
  ] at hbad
  tauto

end ErdosSzekeres

end
