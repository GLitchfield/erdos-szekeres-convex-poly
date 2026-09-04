module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 122. -/

theorem fin15Anchored_clause15616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom1861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01159
  ] at hbad
  tauto

theorem fin15Anchored_clause15617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0574 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0574 Fin15AnchoredAtom1861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01159
  ] at hbad
  tauto

theorem fin15Anchored_clause15618 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1861 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom1861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01159
  ] at hbad
  tauto

theorem fin15Anchored_clause15619 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1861 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0574 chi ∧
      Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom0463 Fin15AnchoredAtom0508
    Fin15AnchoredAtom0574 Fin15AnchoredAtom0860 Fin15AnchoredAtom1861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01159
  ] at hbad
  tauto

theorem fin15Anchored_clause15620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1862 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02183
  ] at hbad
  tauto

theorem fin15Anchored_clause15621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04231
  ] at hbad
  tauto

theorem fin15Anchored_clause15622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04231
  ] at hbad
  tauto

theorem fin15Anchored_clause15623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom1863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04231
  ] at hbad
  tauto

theorem fin15Anchored_clause15624 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0576 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0576 Fin15AnchoredAtom1863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04231
  ] at hbad
  tauto

theorem fin15Anchored_clause15625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1863 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom1863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04231
  ] at hbad
  tauto

theorem fin15Anchored_clause15626 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1863 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0576 chi ∧
      Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom0465 Fin15AnchoredAtom0510
    Fin15AnchoredAtom0576 Fin15AnchoredAtom0862 Fin15AnchoredAtom1863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04231
  ] at hbad
  tauto

theorem fin15Anchored_clause15627 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08327
  ] at hbad
  tauto

theorem fin15Anchored_clause15628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom1864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08327
  ] at hbad
  tauto

theorem fin15Anchored_clause15629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom1864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08327
  ] at hbad
  tauto

theorem fin15Anchored_clause15630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0577 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0577 Fin15AnchoredAtom1864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08327
  ] at hbad
  tauto

theorem fin15Anchored_clause15631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1864 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom1864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08327
  ] at hbad
  tauto

theorem fin15Anchored_clause15632 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1864 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0577 chi ∧
      Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom0466 Fin15AnchoredAtom0511
    Fin15AnchoredAtom0577 Fin15AnchoredAtom0863 Fin15AnchoredAtom1864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08327
  ] at hbad
  tauto

theorem fin15Anchored_clause15633 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0460 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom1865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16519
  ] at hbad
  tauto

theorem fin15Anchored_clause15634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0467 Fin15AnchoredAtom1865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16519
  ] at hbad
  tauto

theorem fin15Anchored_clause15635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom1865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16519
  ] at hbad
  tauto

theorem fin15Anchored_clause15636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0578 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0578 Fin15AnchoredAtom1865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16519
  ] at hbad
  tauto

theorem fin15Anchored_clause15637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1865 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom1865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16519
  ] at hbad
  tauto

theorem fin15Anchored_clause15638 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1865 chi ∧
      Fin15AnchoredAtom0460 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0578 chi ∧
      Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0460 Fin15AnchoredAtom0467 Fin15AnchoredAtom0512
    Fin15AnchoredAtom0578 Fin15AnchoredAtom0864 Fin15AnchoredAtom1865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16519
  ] at hbad
  tauto

theorem fin15Anchored_clause15639 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1866 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00775
  ] at hbad
  tauto

theorem fin15Anchored_clause15640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1866 chi ∧
      ¬Fin15AnchoredAtom0865 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0865 Fin15AnchoredAtom1866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00775
  ] at hbad
  tauto

theorem fin15Anchored_clause15641 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1866 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0579 chi ∧
      Fin15AnchoredAtom0865 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0461 Fin15AnchoredAtom0462 Fin15AnchoredAtom0513
    Fin15AnchoredAtom0579 Fin15AnchoredAtom0865 Fin15AnchoredAtom1866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00775
  ] at hbad
  tauto

theorem fin15Anchored_clause15642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1867 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1867 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01287
  ] at hbad
  tauto

theorem fin15Anchored_clause15643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1867 chi ∧
      ¬Fin15AnchoredAtom0866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0866 Fin15AnchoredAtom1867 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01287
  ] at hbad
  tauto

theorem fin15Anchored_clause15644 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1867 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0580 chi ∧
      Fin15AnchoredAtom0866 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0461 Fin15AnchoredAtom0463 Fin15AnchoredAtom0514
    Fin15AnchoredAtom0580 Fin15AnchoredAtom0866 Fin15AnchoredAtom1867 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01287
  ] at hbad
  tauto

theorem fin15Anchored_clause15645 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1869 chi ∧
      ¬Fin15AnchoredAtom0868 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0868 Fin15AnchoredAtom1869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04359
  ] at hbad
  tauto

theorem fin15Anchored_clause15646 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1869 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0582 chi ∧
      Fin15AnchoredAtom0868 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0461 Fin15AnchoredAtom0465 Fin15AnchoredAtom0516
    Fin15AnchoredAtom0582 Fin15AnchoredAtom0868 Fin15AnchoredAtom1869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04359
  ] at hbad
  tauto

theorem fin15Anchored_clause15647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1871 chi ∧
      ¬Fin15AnchoredAtom0870 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0870 Fin15AnchoredAtom1871 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16647
  ] at hbad
  tauto

theorem fin15Anchored_clause15648 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1871 chi ∧
      Fin15AnchoredAtom0461 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0584 chi ∧
      Fin15AnchoredAtom0870 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0461 Fin15AnchoredAtom0467 Fin15AnchoredAtom0518
    Fin15AnchoredAtom0584 Fin15AnchoredAtom0870 Fin15AnchoredAtom1871 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16647
  ] at hbad
  tauto

theorem fin15Anchored_clause15649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1872 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01543
  ] at hbad
  tauto

theorem fin15Anchored_clause15650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1872 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01543
  ] at hbad
  tauto

theorem fin15Anchored_clause15651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom1872 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01543
  ] at hbad
  tauto

theorem fin15Anchored_clause15652 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0585 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0585 Fin15AnchoredAtom1872 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01543
  ] at hbad
  tauto

theorem fin15Anchored_clause15653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1872 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom1872 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01543
  ] at hbad
  tauto

theorem fin15Anchored_clause15654 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1872 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0585 chi ∧
      Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom0463 Fin15AnchoredAtom0519
    Fin15AnchoredAtom0585 Fin15AnchoredAtom0871 Fin15AnchoredAtom1872 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01543
  ] at hbad
  tauto

theorem fin15Anchored_clause15655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1873 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02567
  ] at hbad
  tauto

theorem fin15Anchored_clause15656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom0464 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0464 Fin15AnchoredAtom1873 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02567
  ] at hbad
  tauto

theorem fin15Anchored_clause15657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom0586 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0586 Fin15AnchoredAtom1873 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02567
  ] at hbad
  tauto

theorem fin15Anchored_clause15658 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1873 chi ∧
      ¬Fin15AnchoredAtom0872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0872 Fin15AnchoredAtom1873 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02567
  ] at hbad
  tauto

theorem fin15Anchored_clause15659 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1873 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0520 chi ∧
      Fin15AnchoredAtom0586 chi ∧
      Fin15AnchoredAtom0872 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom0464 Fin15AnchoredAtom0520
    Fin15AnchoredAtom0586 Fin15AnchoredAtom0872 Fin15AnchoredAtom1873 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02567
  ] at hbad
  tauto

theorem fin15Anchored_clause15660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04615
  ] at hbad
  tauto

theorem fin15Anchored_clause15661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04615
  ] at hbad
  tauto

theorem fin15Anchored_clause15662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom1874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04615
  ] at hbad
  tauto

theorem fin15Anchored_clause15663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0587 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0587 Fin15AnchoredAtom1874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04615
  ] at hbad
  tauto

theorem fin15Anchored_clause15664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1874 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom1874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04615
  ] at hbad
  tauto

theorem fin15Anchored_clause15665 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1874 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0587 chi ∧
      Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom0465 Fin15AnchoredAtom0521
    Fin15AnchoredAtom0587 Fin15AnchoredAtom0873 Fin15AnchoredAtom1874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04615
  ] at hbad
  tauto

theorem fin15Anchored_clause15666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08711
  ] at hbad
  tauto

theorem fin15Anchored_clause15667 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom1875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08711
  ] at hbad
  tauto

theorem fin15Anchored_clause15668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom1875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08711
  ] at hbad
  tauto

theorem fin15Anchored_clause15669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0588 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0588 Fin15AnchoredAtom1875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08711
  ] at hbad
  tauto

theorem fin15Anchored_clause15670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1875 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom1875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08711
  ] at hbad
  tauto

theorem fin15Anchored_clause15671 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1875 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0588 chi ∧
      Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom0466 Fin15AnchoredAtom0522
    Fin15AnchoredAtom0588 Fin15AnchoredAtom0874 Fin15AnchoredAtom1875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08711
  ] at hbad
  tauto

theorem fin15Anchored_clause15672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0462 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom1876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16903
  ] at hbad
  tauto

theorem fin15Anchored_clause15673 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0467 Fin15AnchoredAtom1876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16903
  ] at hbad
  tauto

theorem fin15Anchored_clause15674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom1876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16903
  ] at hbad
  tauto

theorem fin15Anchored_clause15675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0589 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0589 Fin15AnchoredAtom1876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16903
  ] at hbad
  tauto

theorem fin15Anchored_clause15676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1876 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0875 Fin15AnchoredAtom1876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16903
  ] at hbad
  tauto

theorem fin15Anchored_clause15677 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1876 chi ∧
      Fin15AnchoredAtom0462 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0589 chi ∧
      Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0462 Fin15AnchoredAtom0467 Fin15AnchoredAtom0523
    Fin15AnchoredAtom0589 Fin15AnchoredAtom0875 Fin15AnchoredAtom1876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16903
  ] at hbad
  tauto

theorem fin15Anchored_clause15678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1877 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03079
  ] at hbad
  tauto

theorem fin15Anchored_clause15679 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1877 chi ∧
      ¬Fin15AnchoredAtom0590 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0590 Fin15AnchoredAtom1877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03079
  ] at hbad
  tauto

theorem fin15Anchored_clause15680 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1877 chi ∧
      ¬Fin15AnchoredAtom0876 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0876 Fin15AnchoredAtom1877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03079
  ] at hbad
  tauto

theorem fin15Anchored_clause15681 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1877 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0524 chi ∧
      Fin15AnchoredAtom0590 chi ∧
      Fin15AnchoredAtom0876 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom0464 Fin15AnchoredAtom0524
    Fin15AnchoredAtom0590 Fin15AnchoredAtom0876 Fin15AnchoredAtom1877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03079
  ] at hbad
  tauto

theorem fin15Anchored_clause15682 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05127
  ] at hbad
  tauto

theorem fin15Anchored_clause15683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05127
  ] at hbad
  tauto

theorem fin15Anchored_clause15684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom1878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05127
  ] at hbad
  tauto

theorem fin15Anchored_clause15685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0591 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0591 Fin15AnchoredAtom1878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05127
  ] at hbad
  tauto

theorem fin15Anchored_clause15686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1878 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom1878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05127
  ] at hbad
  tauto

theorem fin15Anchored_clause15687 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1878 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0591 chi ∧
      Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom0465 Fin15AnchoredAtom0525
    Fin15AnchoredAtom0591 Fin15AnchoredAtom0877 Fin15AnchoredAtom1878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05127
  ] at hbad
  tauto

theorem fin15Anchored_clause15688 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1879 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09223
  ] at hbad
  tauto

theorem fin15Anchored_clause15689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom1879 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09223
  ] at hbad
  tauto

theorem fin15Anchored_clause15690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom1879 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09223
  ] at hbad
  tauto

theorem fin15Anchored_clause15691 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0592 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0592 Fin15AnchoredAtom1879 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09223
  ] at hbad
  tauto

theorem fin15Anchored_clause15692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1879 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom1879 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09223
  ] at hbad
  tauto

theorem fin15Anchored_clause15693 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1879 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0592 chi ∧
      Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom0466 Fin15AnchoredAtom0526
    Fin15AnchoredAtom0592 Fin15AnchoredAtom0878 Fin15AnchoredAtom1879 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09223
  ] at hbad
  tauto

theorem fin15Anchored_clause15694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0463 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom1880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17415
  ] at hbad
  tauto

theorem fin15Anchored_clause15695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0467 Fin15AnchoredAtom1880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17415
  ] at hbad
  tauto

theorem fin15Anchored_clause15696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom1880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17415
  ] at hbad
  tauto

theorem fin15Anchored_clause15697 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0593 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0593 Fin15AnchoredAtom1880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17415
  ] at hbad
  tauto

theorem fin15Anchored_clause15698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1880 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0879 Fin15AnchoredAtom1880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17415
  ] at hbad
  tauto

theorem fin15Anchored_clause15699 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1880 chi ∧
      Fin15AnchoredAtom0463 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0593 chi ∧
      Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0463 Fin15AnchoredAtom0467 Fin15AnchoredAtom0527
    Fin15AnchoredAtom0593 Fin15AnchoredAtom0879 Fin15AnchoredAtom1880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17415
  ] at hbad
  tauto

theorem fin15Anchored_clause15700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1881 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06151
  ] at hbad
  tauto

theorem fin15Anchored_clause15701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1881 chi ∧
      ¬Fin15AnchoredAtom0594 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0594 Fin15AnchoredAtom1881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06151
  ] at hbad
  tauto

theorem fin15Anchored_clause15702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1881 chi ∧
      ¬Fin15AnchoredAtom0880 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0880 Fin15AnchoredAtom1881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06151
  ] at hbad
  tauto

theorem fin15Anchored_clause15703 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1881 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0594 chi ∧
      Fin15AnchoredAtom0880 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0464 Fin15AnchoredAtom0465 Fin15AnchoredAtom0528
    Fin15AnchoredAtom0594 Fin15AnchoredAtom0880 Fin15AnchoredAtom1881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06151
  ] at hbad
  tauto

theorem fin15Anchored_clause15704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1882 chi ∧
      ¬Fin15AnchoredAtom0881 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0881 Fin15AnchoredAtom1882 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10247
  ] at hbad
  tauto

theorem fin15Anchored_clause15705 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1882 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0595 chi ∧
      Fin15AnchoredAtom0881 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0464 Fin15AnchoredAtom0466 Fin15AnchoredAtom0529
    Fin15AnchoredAtom0595 Fin15AnchoredAtom0881 Fin15AnchoredAtom1882 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10247
  ] at hbad
  tauto

theorem fin15Anchored_clause15706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1883 chi ∧
      ¬Fin15AnchoredAtom0882 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0882 Fin15AnchoredAtom1883 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18439
  ] at hbad
  tauto

theorem fin15Anchored_clause15707 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1883 chi ∧
      Fin15AnchoredAtom0464 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0530 chi ∧
      Fin15AnchoredAtom0596 chi ∧
      Fin15AnchoredAtom0882 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0464 Fin15AnchoredAtom0467 Fin15AnchoredAtom0530
    Fin15AnchoredAtom0596 Fin15AnchoredAtom0882 Fin15AnchoredAtom1883 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18439
  ] at hbad
  tauto

theorem fin15Anchored_clause15708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12295
  ] at hbad
  tauto

theorem fin15Anchored_clause15709 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom1884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12295
  ] at hbad
  tauto

theorem fin15Anchored_clause15710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom1884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12295
  ] at hbad
  tauto

theorem fin15Anchored_clause15711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0597 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0597 Fin15AnchoredAtom1884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12295
  ] at hbad
  tauto

theorem fin15Anchored_clause15712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1884 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom1884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12295
  ] at hbad
  tauto

theorem fin15Anchored_clause15713 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1884 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0597 chi ∧
      Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom0466 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0597 Fin15AnchoredAtom0883 Fin15AnchoredAtom1884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12295
  ] at hbad
  tauto

theorem fin15Anchored_clause15714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0465 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom1885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20487
  ] at hbad
  tauto

theorem fin15Anchored_clause15715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0467 Fin15AnchoredAtom1885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20487
  ] at hbad
  tauto

theorem fin15Anchored_clause15716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom1885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20487
  ] at hbad
  tauto

theorem fin15Anchored_clause15717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0598 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0598 Fin15AnchoredAtom1885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20487
  ] at hbad
  tauto

theorem fin15Anchored_clause15718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1885 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0884 Fin15AnchoredAtom1885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20487
  ] at hbad
  tauto

theorem fin15Anchored_clause15719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1885 chi ∧
      Fin15AnchoredAtom0465 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0532 chi ∧
      Fin15AnchoredAtom0598 chi ∧
      Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0465 Fin15AnchoredAtom0467 Fin15AnchoredAtom0532
    Fin15AnchoredAtom0598 Fin15AnchoredAtom0884 Fin15AnchoredAtom1885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20487
  ] at hbad
  tauto

theorem fin15Anchored_clause15720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0466 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom1886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24583
  ] at hbad
  tauto

theorem fin15Anchored_clause15721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0467 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0467 Fin15AnchoredAtom1886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24583
  ] at hbad
  tauto

theorem fin15Anchored_clause15722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0533 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0533 Fin15AnchoredAtom1886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24583
  ] at hbad
  tauto

theorem fin15Anchored_clause15723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0599 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0599 Fin15AnchoredAtom1886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24583
  ] at hbad
  tauto

theorem fin15Anchored_clause15724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1886 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0885 Fin15AnchoredAtom1886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24583
  ] at hbad
  tauto

theorem fin15Anchored_clause15725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1886 chi ∧
      Fin15AnchoredAtom0466 chi ∧
      Fin15AnchoredAtom0467 chi ∧
      Fin15AnchoredAtom0533 chi ∧
      Fin15AnchoredAtom0599 chi ∧
      Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0466 Fin15AnchoredAtom0467 Fin15AnchoredAtom0533
    Fin15AnchoredAtom0599 Fin15AnchoredAtom0885 Fin15AnchoredAtom1886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24583
  ] at hbad
  tauto

theorem fin15Anchored_clause15726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00059
  ] at hbad
  tauto

theorem fin15Anchored_clause15727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0469 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0469 Fin15AnchoredAtom1887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00059
  ] at hbad
  tauto

theorem fin15Anchored_clause15728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0479 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0479 Fin15AnchoredAtom1887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00059
  ] at hbad
  tauto

theorem fin15Anchored_clause15729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0600 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0600 Fin15AnchoredAtom1887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00059
  ] at hbad
  tauto

theorem fin15Anchored_clause15730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1887 chi ∧
      ¬Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0886 Fin15AnchoredAtom1887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00059
  ] at hbad
  tauto

theorem fin15Anchored_clause15731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1887 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0469 chi ∧
      Fin15AnchoredAtom0479 chi ∧
      Fin15AnchoredAtom0600 chi ∧
      Fin15AnchoredAtom0886 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0469 Fin15AnchoredAtom0479
    Fin15AnchoredAtom0600 Fin15AnchoredAtom0886 Fin15AnchoredAtom1887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00059
  ] at hbad
  tauto

theorem fin15Anchored_clause15732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00091
  ] at hbad
  tauto

theorem fin15Anchored_clause15733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0470 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0470 Fin15AnchoredAtom1888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00091
  ] at hbad
  tauto

theorem fin15Anchored_clause15734 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0480 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0480 Fin15AnchoredAtom1888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00091
  ] at hbad
  tauto

theorem fin15Anchored_clause15735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0601 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0601 Fin15AnchoredAtom1888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00091
  ] at hbad
  tauto

theorem fin15Anchored_clause15736 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1888 chi ∧
      ¬Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0887 Fin15AnchoredAtom1888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00091
  ] at hbad
  tauto

theorem fin15Anchored_clause15737 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1888 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0470 chi ∧
      Fin15AnchoredAtom0480 chi ∧
      Fin15AnchoredAtom0601 chi ∧
      Fin15AnchoredAtom0887 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0470 Fin15AnchoredAtom0480
    Fin15AnchoredAtom0601 Fin15AnchoredAtom0887 Fin15AnchoredAtom1888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00091
  ] at hbad
  tauto

theorem fin15Anchored_clause15738 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0468 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom1889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00155
  ] at hbad
  tauto

theorem fin15Anchored_clause15739 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0471 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0471 Fin15AnchoredAtom1889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00155
  ] at hbad
  tauto

theorem fin15Anchored_clause15740 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00155
  ] at hbad
  tauto

theorem fin15Anchored_clause15741 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0602 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0602 Fin15AnchoredAtom1889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00155
  ] at hbad
  tauto

theorem fin15Anchored_clause15742 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1889 chi ∧
      ¬Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0888 Fin15AnchoredAtom1889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00155
  ] at hbad
  tauto

theorem fin15Anchored_clause15743 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1889 chi ∧
      Fin15AnchoredAtom0468 chi ∧
      Fin15AnchoredAtom0471 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0602 chi ∧
      Fin15AnchoredAtom0888 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0468 Fin15AnchoredAtom0471 Fin15AnchoredAtom0481
    Fin15AnchoredAtom0602 Fin15AnchoredAtom0888 Fin15AnchoredAtom1889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00155
  ] at hbad
  tauto

end ErdosSzekeres

end
