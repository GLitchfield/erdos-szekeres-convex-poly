module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 159. -/

theorem fin15Anchored_clause20352 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom0893 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0893 Fin15AnchoredAtom2829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04126
  ] at hbad
  tauto

theorem fin15Anchored_clause20353 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2829 chi ∧
      ¬Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1113 Fin15AnchoredAtom2829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04126
  ] at hbad
  tauto

theorem fin15Anchored_clause20354 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2829 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0893 chi ∧
      Fin15AnchoredAtom1113 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom0828 Fin15AnchoredAtom0838
    Fin15AnchoredAtom0893 Fin15AnchoredAtom1113 Fin15AnchoredAtom2829 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04126
  ] at hbad
  tauto

theorem fin15Anchored_clause20355 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom2830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08222
  ] at hbad
  tauto

theorem fin15Anchored_clause20356 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom2830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08222
  ] at hbad
  tauto

theorem fin15Anchored_clause20357 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom2830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08222
  ] at hbad
  tauto

theorem fin15Anchored_clause20358 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom0894 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0894 Fin15AnchoredAtom2830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08222
  ] at hbad
  tauto

theorem fin15Anchored_clause20359 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2830 chi ∧
      ¬Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1114 Fin15AnchoredAtom2830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08222
  ] at hbad
  tauto

theorem fin15Anchored_clause20360 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2830 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0894 chi ∧
      Fin15AnchoredAtom1114 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom0829 Fin15AnchoredAtom0839
    Fin15AnchoredAtom0894 Fin15AnchoredAtom1114 Fin15AnchoredAtom2830 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08222
  ] at hbad
  tauto

theorem fin15Anchored_clause20361 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom0820 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom2831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16414
  ] at hbad
  tauto

theorem fin15Anchored_clause20362 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16414
  ] at hbad
  tauto

theorem fin15Anchored_clause20363 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom2831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16414
  ] at hbad
  tauto

theorem fin15Anchored_clause20364 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom0895 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0895 Fin15AnchoredAtom2831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16414
  ] at hbad
  tauto

theorem fin15Anchored_clause20365 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2831 chi ∧
      ¬Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1115 Fin15AnchoredAtom2831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16414
  ] at hbad
  tauto

theorem fin15Anchored_clause20366 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2831 chi ∧
      Fin15AnchoredAtom0820 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0895 chi ∧
      Fin15AnchoredAtom1115 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0820 Fin15AnchoredAtom0830 Fin15AnchoredAtom0840
    Fin15AnchoredAtom0895 Fin15AnchoredAtom1115 Fin15AnchoredAtom2831 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16414
  ] at hbad
  tauto

theorem fin15Anchored_clause20367 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom2832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00110
  ] at hbad
  tauto

theorem fin15Anchored_clause20368 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00110
  ] at hbad
  tauto

theorem fin15Anchored_clause20369 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom2832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00110
  ] at hbad
  tauto

theorem fin15Anchored_clause20370 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom0896 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0896 Fin15AnchoredAtom2832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00110
  ] at hbad
  tauto

theorem fin15Anchored_clause20371 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2832 chi ∧
      ¬Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1116 Fin15AnchoredAtom2832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00110
  ] at hbad
  tauto

theorem fin15Anchored_clause20372 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2832 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0896 chi ∧
      Fin15AnchoredAtom1116 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom0822 Fin15AnchoredAtom0841
    Fin15AnchoredAtom0896 Fin15AnchoredAtom1116 Fin15AnchoredAtom2832 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00110
  ] at hbad
  tauto

theorem fin15Anchored_clause20373 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom2833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00174
  ] at hbad
  tauto

theorem fin15Anchored_clause20374 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00174
  ] at hbad
  tauto

theorem fin15Anchored_clause20375 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom2833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00174
  ] at hbad
  tauto

theorem fin15Anchored_clause20376 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom0897 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0897 Fin15AnchoredAtom2833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00174
  ] at hbad
  tauto

theorem fin15Anchored_clause20377 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2833 chi ∧
      ¬Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1117 Fin15AnchoredAtom2833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00174
  ] at hbad
  tauto

theorem fin15Anchored_clause20378 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2833 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0897 chi ∧
      Fin15AnchoredAtom1117 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom0823 Fin15AnchoredAtom0842
    Fin15AnchoredAtom0897 Fin15AnchoredAtom1117 Fin15AnchoredAtom2833 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00174
  ] at hbad
  tauto

theorem fin15Anchored_clause20379 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2834 chi ∧
      ¬Fin15AnchoredAtom1118 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1118 Fin15AnchoredAtom2834 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00302
  ] at hbad
  tauto

theorem fin15Anchored_clause20380 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2834 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0824 chi ∧
      Fin15AnchoredAtom0843 chi ∧
      Fin15AnchoredAtom0898 chi ∧
      Fin15AnchoredAtom1118 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom0824 Fin15AnchoredAtom0843
    Fin15AnchoredAtom0898 Fin15AnchoredAtom1118 Fin15AnchoredAtom2834 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00302
  ] at hbad
  tauto

theorem fin15Anchored_clause20381 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom2835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00558
  ] at hbad
  tauto

theorem fin15Anchored_clause20382 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom2835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00558
  ] at hbad
  tauto

theorem fin15Anchored_clause20383 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom2835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00558
  ] at hbad
  tauto

theorem fin15Anchored_clause20384 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom0899 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0899 Fin15AnchoredAtom2835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00558
  ] at hbad
  tauto

theorem fin15Anchored_clause20385 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2835 chi ∧
      ¬Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1119 Fin15AnchoredAtom2835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00558
  ] at hbad
  tauto

theorem fin15Anchored_clause20386 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2835 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0899 chi ∧
      Fin15AnchoredAtom1119 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom0825 Fin15AnchoredAtom0844
    Fin15AnchoredAtom0899 Fin15AnchoredAtom1119 Fin15AnchoredAtom2835 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00558
  ] at hbad
  tauto

theorem fin15Anchored_clause20387 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom2836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01070
  ] at hbad
  tauto

theorem fin15Anchored_clause20388 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom2836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01070
  ] at hbad
  tauto

theorem fin15Anchored_clause20389 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom2836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01070
  ] at hbad
  tauto

theorem fin15Anchored_clause20390 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom0900 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0900 Fin15AnchoredAtom2836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01070
  ] at hbad
  tauto

theorem fin15Anchored_clause20391 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2836 chi ∧
      ¬Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1120 Fin15AnchoredAtom2836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01070
  ] at hbad
  tauto

theorem fin15Anchored_clause20392 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2836 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0900 chi ∧
      Fin15AnchoredAtom1120 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom0826 Fin15AnchoredAtom0845
    Fin15AnchoredAtom0900 Fin15AnchoredAtom1120 Fin15AnchoredAtom2836 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01070
  ] at hbad
  tauto

theorem fin15Anchored_clause20393 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2837 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom2837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02094
  ] at hbad
  tauto

theorem fin15Anchored_clause20394 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2837 chi ∧
      ¬Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1121 Fin15AnchoredAtom2837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02094
  ] at hbad
  tauto

theorem fin15Anchored_clause20395 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2837 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0846 chi ∧
      Fin15AnchoredAtom0901 chi ∧
      Fin15AnchoredAtom1121 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom0827 Fin15AnchoredAtom0846
    Fin15AnchoredAtom0901 Fin15AnchoredAtom1121 Fin15AnchoredAtom2837 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02094
  ] at hbad
  tauto

theorem fin15Anchored_clause20396 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom2838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04142
  ] at hbad
  tauto

theorem fin15Anchored_clause20397 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom2838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04142
  ] at hbad
  tauto

theorem fin15Anchored_clause20398 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom2838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04142
  ] at hbad
  tauto

theorem fin15Anchored_clause20399 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom0902 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0902 Fin15AnchoredAtom2838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04142
  ] at hbad
  tauto

theorem fin15Anchored_clause20400 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2838 chi ∧
      ¬Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1122 Fin15AnchoredAtom2838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04142
  ] at hbad
  tauto

theorem fin15Anchored_clause20401 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2838 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0902 chi ∧
      Fin15AnchoredAtom1122 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom0828 Fin15AnchoredAtom0847
    Fin15AnchoredAtom0902 Fin15AnchoredAtom1122 Fin15AnchoredAtom2838 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04142
  ] at hbad
  tauto

theorem fin15Anchored_clause20402 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom2839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08238
  ] at hbad
  tauto

theorem fin15Anchored_clause20403 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom2839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08238
  ] at hbad
  tauto

theorem fin15Anchored_clause20404 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom2839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08238
  ] at hbad
  tauto

theorem fin15Anchored_clause20405 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom0903 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0903 Fin15AnchoredAtom2839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08238
  ] at hbad
  tauto

theorem fin15Anchored_clause20406 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2839 chi ∧
      ¬Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1123 Fin15AnchoredAtom2839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08238
  ] at hbad
  tauto

theorem fin15Anchored_clause20407 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2839 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0903 chi ∧
      Fin15AnchoredAtom1123 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom0829 Fin15AnchoredAtom0848
    Fin15AnchoredAtom0903 Fin15AnchoredAtom1123 Fin15AnchoredAtom2839 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08238
  ] at hbad
  tauto

theorem fin15Anchored_clause20408 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom0821 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom2840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16430
  ] at hbad
  tauto

theorem fin15Anchored_clause20409 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16430
  ] at hbad
  tauto

theorem fin15Anchored_clause20410 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0849 Fin15AnchoredAtom2840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16430
  ] at hbad
  tauto

theorem fin15Anchored_clause20411 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom0904 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0904 Fin15AnchoredAtom2840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16430
  ] at hbad
  tauto

theorem fin15Anchored_clause20412 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2840 chi ∧
      ¬Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1124 Fin15AnchoredAtom2840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16430
  ] at hbad
  tauto

theorem fin15Anchored_clause20413 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2840 chi ∧
      Fin15AnchoredAtom0821 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0904 chi ∧
      Fin15AnchoredAtom1124 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0821 Fin15AnchoredAtom0830 Fin15AnchoredAtom0849
    Fin15AnchoredAtom0904 Fin15AnchoredAtom1124 Fin15AnchoredAtom2840 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16430
  ] at hbad
  tauto

theorem fin15Anchored_clause20414 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00206
  ] at hbad
  tauto

theorem fin15Anchored_clause20415 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00206
  ] at hbad
  tauto

theorem fin15Anchored_clause20416 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00206
  ] at hbad
  tauto

theorem fin15Anchored_clause20417 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom0905 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0905 Fin15AnchoredAtom2841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00206
  ] at hbad
  tauto

theorem fin15Anchored_clause20418 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2841 chi ∧
      ¬Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1125 Fin15AnchoredAtom2841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00206
  ] at hbad
  tauto

theorem fin15Anchored_clause20419 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2841 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0905 chi ∧
      Fin15AnchoredAtom1125 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom0823 Fin15AnchoredAtom0850
    Fin15AnchoredAtom0905 Fin15AnchoredAtom1125 Fin15AnchoredAtom2841 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00206
  ] at hbad
  tauto

theorem fin15Anchored_clause20420 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2842 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2842 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00334
  ] at hbad
  tauto

theorem fin15Anchored_clause20421 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00590
  ] at hbad
  tauto

theorem fin15Anchored_clause20422 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom2843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00590
  ] at hbad
  tauto

theorem fin15Anchored_clause20423 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom2843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00590
  ] at hbad
  tauto

theorem fin15Anchored_clause20424 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom0907 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0907 Fin15AnchoredAtom2843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00590
  ] at hbad
  tauto

theorem fin15Anchored_clause20425 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2843 chi ∧
      ¬Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1127 Fin15AnchoredAtom2843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00590
  ] at hbad
  tauto

theorem fin15Anchored_clause20426 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2843 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0907 chi ∧
      Fin15AnchoredAtom1127 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom0825 Fin15AnchoredAtom0852
    Fin15AnchoredAtom0907 Fin15AnchoredAtom1127 Fin15AnchoredAtom2843 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00590
  ] at hbad
  tauto

theorem fin15Anchored_clause20427 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01102
  ] at hbad
  tauto

theorem fin15Anchored_clause20428 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom2844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01102
  ] at hbad
  tauto

theorem fin15Anchored_clause20429 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01102
  ] at hbad
  tauto

theorem fin15Anchored_clause20430 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom0908 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0908 Fin15AnchoredAtom2844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01102
  ] at hbad
  tauto

theorem fin15Anchored_clause20431 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2844 chi ∧
      ¬Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1128 Fin15AnchoredAtom2844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01102
  ] at hbad
  tauto

theorem fin15Anchored_clause20432 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2844 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0908 chi ∧
      Fin15AnchoredAtom1128 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom0826 Fin15AnchoredAtom0853
    Fin15AnchoredAtom0908 Fin15AnchoredAtom1128 Fin15AnchoredAtom2844 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01102
  ] at hbad
  tauto

theorem fin15Anchored_clause20433 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2845 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2845 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02126
  ] at hbad
  tauto

theorem fin15Anchored_clause20434 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04174
  ] at hbad
  tauto

theorem fin15Anchored_clause20435 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom2846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04174
  ] at hbad
  tauto

theorem fin15Anchored_clause20436 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom2846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04174
  ] at hbad
  tauto

theorem fin15Anchored_clause20437 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom0910 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0910 Fin15AnchoredAtom2846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04174
  ] at hbad
  tauto

theorem fin15Anchored_clause20438 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2846 chi ∧
      ¬Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1130 Fin15AnchoredAtom2846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04174
  ] at hbad
  tauto

theorem fin15Anchored_clause20439 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2846 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0910 chi ∧
      Fin15AnchoredAtom1130 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom0828 Fin15AnchoredAtom0855
    Fin15AnchoredAtom0910 Fin15AnchoredAtom1130 Fin15AnchoredAtom2846 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04174
  ] at hbad
  tauto

theorem fin15Anchored_clause20440 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08270
  ] at hbad
  tauto

theorem fin15Anchored_clause20441 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom2847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08270
  ] at hbad
  tauto

theorem fin15Anchored_clause20442 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom2847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08270
  ] at hbad
  tauto

theorem fin15Anchored_clause20443 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom0911 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0911 Fin15AnchoredAtom2847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08270
  ] at hbad
  tauto

theorem fin15Anchored_clause20444 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2847 chi ∧
      ¬Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1131 Fin15AnchoredAtom2847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08270
  ] at hbad
  tauto

theorem fin15Anchored_clause20445 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2847 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0911 chi ∧
      Fin15AnchoredAtom1131 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom0829 Fin15AnchoredAtom0856
    Fin15AnchoredAtom0911 Fin15AnchoredAtom1131 Fin15AnchoredAtom2847 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08270
  ] at hbad
  tauto

theorem fin15Anchored_clause20446 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom0822 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom2848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16462
  ] at hbad
  tauto

theorem fin15Anchored_clause20447 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16462
  ] at hbad
  tauto

theorem fin15Anchored_clause20448 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom2848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16462
  ] at hbad
  tauto

theorem fin15Anchored_clause20449 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom0912 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0912 Fin15AnchoredAtom2848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16462
  ] at hbad
  tauto

theorem fin15Anchored_clause20450 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2848 chi ∧
      ¬Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1132 Fin15AnchoredAtom2848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16462
  ] at hbad
  tauto

theorem fin15Anchored_clause20451 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2848 chi ∧
      Fin15AnchoredAtom0822 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0912 chi ∧
      Fin15AnchoredAtom1132 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0822 Fin15AnchoredAtom0830 Fin15AnchoredAtom0857
    Fin15AnchoredAtom0912 Fin15AnchoredAtom1132 Fin15AnchoredAtom2848 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16462
  ] at hbad
  tauto

theorem fin15Anchored_clause20452 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2849 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00398
  ] at hbad
  tauto

theorem fin15Anchored_clause20453 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2849 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0824 chi ∧
      Fin15AnchoredAtom0858 chi ∧
      Fin15AnchoredAtom0913 chi ∧
      Fin15AnchoredAtom1133 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom0824 Fin15AnchoredAtom0858
    Fin15AnchoredAtom0913 Fin15AnchoredAtom1133 Fin15AnchoredAtom2849 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00398
  ] at hbad
  tauto

theorem fin15Anchored_clause20454 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00654
  ] at hbad
  tauto

theorem fin15Anchored_clause20455 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom2850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00654
  ] at hbad
  tauto

theorem fin15Anchored_clause20456 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom2850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00654
  ] at hbad
  tauto

theorem fin15Anchored_clause20457 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom0914 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0914 Fin15AnchoredAtom2850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00654
  ] at hbad
  tauto

theorem fin15Anchored_clause20458 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2850 chi ∧
      ¬Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1134 Fin15AnchoredAtom2850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00654
  ] at hbad
  tauto

theorem fin15Anchored_clause20459 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2850 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0914 chi ∧
      Fin15AnchoredAtom1134 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom0825 Fin15AnchoredAtom0859
    Fin15AnchoredAtom0914 Fin15AnchoredAtom1134 Fin15AnchoredAtom2850 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00654
  ] at hbad
  tauto

theorem fin15Anchored_clause20460 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01166
  ] at hbad
  tauto

theorem fin15Anchored_clause20461 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom2851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01166
  ] at hbad
  tauto

theorem fin15Anchored_clause20462 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom2851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01166
  ] at hbad
  tauto

theorem fin15Anchored_clause20463 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom0915 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0915 Fin15AnchoredAtom2851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01166
  ] at hbad
  tauto

theorem fin15Anchored_clause20464 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2851 chi ∧
      ¬Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1135 Fin15AnchoredAtom2851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01166
  ] at hbad
  tauto

theorem fin15Anchored_clause20465 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2851 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0915 chi ∧
      Fin15AnchoredAtom1135 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom0826 Fin15AnchoredAtom0860
    Fin15AnchoredAtom0915 Fin15AnchoredAtom1135 Fin15AnchoredAtom2851 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01166
  ] at hbad
  tauto

theorem fin15Anchored_clause20466 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2852 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2852 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02190
  ] at hbad
  tauto

theorem fin15Anchored_clause20467 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04238
  ] at hbad
  tauto

theorem fin15Anchored_clause20468 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom2853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04238
  ] at hbad
  tauto

theorem fin15Anchored_clause20469 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom2853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04238
  ] at hbad
  tauto

theorem fin15Anchored_clause20470 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom0917 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0917 Fin15AnchoredAtom2853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04238
  ] at hbad
  tauto

theorem fin15Anchored_clause20471 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2853 chi ∧
      ¬Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1137 Fin15AnchoredAtom2853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04238
  ] at hbad
  tauto

theorem fin15Anchored_clause20472 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2853 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0917 chi ∧
      Fin15AnchoredAtom1137 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom0828 Fin15AnchoredAtom0862
    Fin15AnchoredAtom0917 Fin15AnchoredAtom1137 Fin15AnchoredAtom2853 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04238
  ] at hbad
  tauto

theorem fin15Anchored_clause20473 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08334
  ] at hbad
  tauto

theorem fin15Anchored_clause20474 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom2854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08334
  ] at hbad
  tauto

theorem fin15Anchored_clause20475 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom2854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08334
  ] at hbad
  tauto

theorem fin15Anchored_clause20476 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom0918 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0918 Fin15AnchoredAtom2854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08334
  ] at hbad
  tauto

theorem fin15Anchored_clause20477 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2854 chi ∧
      ¬Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1138 Fin15AnchoredAtom2854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08334
  ] at hbad
  tauto

theorem fin15Anchored_clause20478 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2854 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0918 chi ∧
      Fin15AnchoredAtom1138 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom0829 Fin15AnchoredAtom0863
    Fin15AnchoredAtom0918 Fin15AnchoredAtom1138 Fin15AnchoredAtom2854 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08334
  ] at hbad
  tauto

theorem fin15Anchored_clause20479 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom0823 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom2855 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16526
  ] at hbad
  tauto

end ErdosSzekeres

end
