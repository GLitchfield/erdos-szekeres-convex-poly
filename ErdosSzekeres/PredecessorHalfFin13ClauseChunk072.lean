module

public import ErdosSzekeres.PredecessorHalfFin13Support

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained Fin13 semantic clauses in bounded group 072. -/

theorem predecessorHalfFin13_clause22306 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0740 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0740 PredecessorHalfFin13Atom1859 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22307 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1859 chi ∧
      ¬PredecessorHalfFin13Atom0824 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0824 PredecessorHalfFin13Atom1859 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2156
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22309 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0680 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom1860 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22310 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom1860 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22311 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom1860 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22312 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0741 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom1860 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22313 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1860 chi ∧
      ¬PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom1860 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22314 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1860 chi ∧
      PredecessorHalfFin13Atom0680 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0741 chi ∧
      PredecessorHalfFin13Atom0825 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0680 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0692
    PredecessorHalfFin13Atom0741 PredecessorHalfFin13Atom0825 PredecessorHalfFin13Atom1860 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4204
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22315 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom1861 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22316 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom1861 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22317 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom1861 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22318 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0742 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom1861 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22319 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1861 chi ∧
      ¬PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom1861 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22320 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1861 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0742 chi ∧
      PredecessorHalfFin13Atom0826 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0693
    PredecessorHalfFin13Atom0742 PredecessorHalfFin13Atom0826 PredecessorHalfFin13Atom1861 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0428
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22321 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom1862 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22322 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom1862 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22323 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom1862 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22324 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0743 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom1862 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22325 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1862 chi ∧
      ¬PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom1862 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22326 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1862 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0743 chi ∧
      PredecessorHalfFin13Atom0827 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0694
    PredecessorHalfFin13Atom0743 PredecessorHalfFin13Atom0827 PredecessorHalfFin13Atom1862 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0684
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22327 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom1863 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22328 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom1863 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22329 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom1863 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22330 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0744 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom1863 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22331 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1863 chi ∧
      ¬PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom1863 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22332 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1863 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0744 chi ∧
      PredecessorHalfFin13Atom0828 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0695
    PredecessorHalfFin13Atom0744 PredecessorHalfFin13Atom0828 PredecessorHalfFin13Atom1863 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1196
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22333 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom1864 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22334 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom1864 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22335 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom1864 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22336 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0745 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0745 PredecessorHalfFin13Atom1864 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22337 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1864 chi ∧
      ¬PredecessorHalfFin13Atom0829 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0829 PredecessorHalfFin13Atom1864 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2220
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22339 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0681 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom1865 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22340 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom1865 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22341 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom1865 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22342 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0746 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom1865 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22343 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1865 chi ∧
      ¬PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom1865 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22344 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1865 chi ∧
      PredecessorHalfFin13Atom0681 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0746 chi ∧
      PredecessorHalfFin13Atom0830 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0681 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0746 PredecessorHalfFin13Atom0830 PredecessorHalfFin13Atom1865 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4268
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22345 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom1866 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22346 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom1866 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22347 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom1866 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22348 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0747 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom1866 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22349 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1866 chi ∧
      ¬PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom1866 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22350 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1866 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0747 chi ∧
      PredecessorHalfFin13Atom0831 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0747 PredecessorHalfFin13Atom0831 PredecessorHalfFin13Atom1866 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0812
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22351 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom1867 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22352 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom1867 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22353 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0699 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0699 PredecessorHalfFin13Atom1867 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22354 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0748 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom1867 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22355 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1867 chi ∧
      ¬PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom1867 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22356 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1867 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0699 chi ∧
      PredecessorHalfFin13Atom0748 chi ∧
      PredecessorHalfFin13Atom0832 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0699
    PredecessorHalfFin13Atom0748 PredecessorHalfFin13Atom0832 PredecessorHalfFin13Atom1867 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1324
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22357 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom1868 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22358 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom1868 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22359 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0700 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0700 PredecessorHalfFin13Atom1868 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22360 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0749 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0749 PredecessorHalfFin13Atom1868 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22361 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1868 chi ∧
      ¬PredecessorHalfFin13Atom0833 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0833 PredecessorHalfFin13Atom1868 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2348
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22363 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0682 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom1869 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22364 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom1869 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22365 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0701 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0701 PredecessorHalfFin13Atom1869 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22366 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0750 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom1869 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22367 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1869 chi ∧
      ¬PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom1869 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22368 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1869 chi ∧
      PredecessorHalfFin13Atom0682 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0701 chi ∧
      PredecessorHalfFin13Atom0750 chi ∧
      PredecessorHalfFin13Atom0834 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0682 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0701
    PredecessorHalfFin13Atom0750 PredecessorHalfFin13Atom0834 PredecessorHalfFin13Atom1869 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4396
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22369 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom1870 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1580
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22370 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom1870 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1580
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22371 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0702 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0702 PredecessorHalfFin13Atom1870 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1580
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22372 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0751 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom1870 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1580
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22373 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1870 chi ∧
      ¬PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom1870 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1580
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22374 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1870 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0702 chi ∧
      PredecessorHalfFin13Atom0751 chi ∧
      PredecessorHalfFin13Atom0835 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0702
    PredecessorHalfFin13Atom0751 PredecessorHalfFin13Atom0835 PredecessorHalfFin13Atom1870 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1580
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22375 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom1871 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22376 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom1871 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22377 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0703 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0703 PredecessorHalfFin13Atom1871 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22378 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0752 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0752 PredecessorHalfFin13Atom1871 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22379 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1871 chi ∧
      ¬PredecessorHalfFin13Atom0836 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0836 PredecessorHalfFin13Atom1871 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2604
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22381 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0683 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom1872 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22382 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom1872 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22383 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0704 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0704 PredecessorHalfFin13Atom1872 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22384 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0753 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom1872 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22385 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1872 chi ∧
      ¬PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom1872 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22386 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1872 chi ∧
      PredecessorHalfFin13Atom0683 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0704 chi ∧
      PredecessorHalfFin13Atom0753 chi ∧
      PredecessorHalfFin13Atom0837 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0683 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0704
    PredecessorHalfFin13Atom0753 PredecessorHalfFin13Atom0837 PredecessorHalfFin13Atom1872 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4652
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22387 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom1873 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22388 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom1873 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22389 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0705 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0705 PredecessorHalfFin13Atom1873 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22390 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0754 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom1873 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22391 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1873 chi ∧
      ¬PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom1873 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22392 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1873 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0685 chi ∧
      PredecessorHalfFin13Atom0705 chi ∧
      PredecessorHalfFin13Atom0754 chi ∧
      PredecessorHalfFin13Atom0838 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom0705
    PredecessorHalfFin13Atom0754 PredecessorHalfFin13Atom0838 PredecessorHalfFin13Atom1873 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask3116
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22393 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0684 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom1874 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22394 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom1874 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22395 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0706 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0706 PredecessorHalfFin13Atom1874 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22396 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0755 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom1874 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22397 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1874 chi ∧
      ¬PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom1874 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22398 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1874 chi ∧
      PredecessorHalfFin13Atom0684 chi ∧
      PredecessorHalfFin13Atom0686 chi ∧
      PredecessorHalfFin13Atom0706 chi ∧
      PredecessorHalfFin13Atom0755 chi ∧
      PredecessorHalfFin13Atom0839 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0684 PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom0706
    PredecessorHalfFin13Atom0755 PredecessorHalfFin13Atom0839 PredecessorHalfFin13Atom1874 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask5164
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22399 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0685 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0685 PredecessorHalfFin13Atom1875 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22400 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0686 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0686 PredecessorHalfFin13Atom1875 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22401 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0707 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0707 PredecessorHalfFin13Atom1875 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22402 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0756 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0756 PredecessorHalfFin13Atom1875 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22403 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1875 chi ∧
      ¬PredecessorHalfFin13Atom0840 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0840 PredecessorHalfFin13Atom1875 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask6188
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22405 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom1876 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22406 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom1876 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22407 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0693 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0693 PredecessorHalfFin13Atom1876 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22408 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0757 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom1876 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22409 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1876 chi ∧
      ¬PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom1876 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22410 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1876 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0693 chi ∧
      PredecessorHalfFin13Atom0757 chi ∧
      PredecessorHalfFin13Atom0841 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0693
    PredecessorHalfFin13Atom0757 PredecessorHalfFin13Atom0841 PredecessorHalfFin13Atom1876 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0460
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22411 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom1877 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0716
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22412 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom1877 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0716
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22413 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0694 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0694 PredecessorHalfFin13Atom1877 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0716
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22414 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0758 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom1877 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0716
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22415 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1877 chi ∧
      ¬PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom1877 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0716
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22416 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1877 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0694 chi ∧
      PredecessorHalfFin13Atom0758 chi ∧
      PredecessorHalfFin13Atom0842 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0694
    PredecessorHalfFin13Atom0758 PredecessorHalfFin13Atom0842 PredecessorHalfFin13Atom1877 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0716
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22417 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom1878 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22418 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0690 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom1878 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22419 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0695 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0695 PredecessorHalfFin13Atom1878 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22420 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0759 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom1878 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22421 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1878 chi ∧
      ¬PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom1878 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22422 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1878 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0690 chi ∧
      PredecessorHalfFin13Atom0695 chi ∧
      PredecessorHalfFin13Atom0759 chi ∧
      PredecessorHalfFin13Atom0843 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0690 PredecessorHalfFin13Atom0695
    PredecessorHalfFin13Atom0759 PredecessorHalfFin13Atom0843 PredecessorHalfFin13Atom1878 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask1228
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22423 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom1879 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22425 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom0696 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0696 PredecessorHalfFin13Atom1879 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22426 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom0760 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0760 PredecessorHalfFin13Atom1879 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22427 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1879 chi ∧
      ¬PredecessorHalfFin13Atom0844 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0844 PredecessorHalfFin13Atom1879 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask2252
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22429 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0687 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom1880 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22430 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0692 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom1880 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22431 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0697 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0697 PredecessorHalfFin13Atom1880 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22432 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0761 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom1880 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22433 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1880 chi ∧
      ¬PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom1880 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22434 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1880 chi ∧
      PredecessorHalfFin13Atom0687 chi ∧
      PredecessorHalfFin13Atom0692 chi ∧
      PredecessorHalfFin13Atom0697 chi ∧
      PredecessorHalfFin13Atom0761 chi ∧
      PredecessorHalfFin13Atom0845 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0687 PredecessorHalfFin13Atom0692 PredecessorHalfFin13Atom0697
    PredecessorHalfFin13Atom0761 PredecessorHalfFin13Atom0845 PredecessorHalfFin13Atom1880 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask4300
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22435 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0688 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom1881 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22436 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0689 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom1881 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22437 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0698 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0698 PredecessorHalfFin13Atom1881 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22438 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0762 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom1881 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22439 (chi : TripleColoring 13)
    : ¬(PredecessorHalfFin13Atom1881 chi ∧
      ¬PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom1881 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0844
  ] at hbad
  tauto

theorem predecessorHalfFin13_clause22440 (chi : TripleColoring 13)
    : ¬(¬PredecessorHalfFin13Atom1881 chi ∧
      PredecessorHalfFin13Atom0688 chi ∧
      PredecessorHalfFin13Atom0689 chi ∧
      PredecessorHalfFin13Atom0698 chi ∧
      PredecessorHalfFin13Atom0762 chi ∧
      PredecessorHalfFin13Atom0846 chi) := by
  intro hbad
  unfold PredecessorHalfFin13Atom0688 PredecessorHalfFin13Atom0689 PredecessorHalfFin13Atom0698
    PredecessorHalfFin13Atom0762 PredecessorHalfFin13Atom0846 PredecessorHalfFin13Atom1881 at hbad
  simp only [
    predecessorHalfFin13_strongSet_iff_mask0844
  ] at hbad
  tauto

end ErdosSzekeres

end
