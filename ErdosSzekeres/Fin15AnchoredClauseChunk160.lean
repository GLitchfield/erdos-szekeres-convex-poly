module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 160. -/

theorem fin15Anchored_clause20480 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2855 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16526
  ] at hbad
  tauto

theorem fin15Anchored_clause20481 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom2855 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16526
  ] at hbad
  tauto

theorem fin15Anchored_clause20482 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom0919 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0919 Fin15AnchoredAtom2855 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16526
  ] at hbad
  tauto

theorem fin15Anchored_clause20483 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2855 chi ∧
      ¬Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1139 Fin15AnchoredAtom2855 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16526
  ] at hbad
  tauto

theorem fin15Anchored_clause20484 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2855 chi ∧
      Fin15AnchoredAtom0823 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0919 chi ∧
      Fin15AnchoredAtom1139 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0823 Fin15AnchoredAtom0830 Fin15AnchoredAtom0864
    Fin15AnchoredAtom0919 Fin15AnchoredAtom1139 Fin15AnchoredAtom2855 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16526
  ] at hbad
  tauto

theorem fin15Anchored_clause20485 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2857 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom2857 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01294
  ] at hbad
  tauto

theorem fin15Anchored_clause20486 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2857 chi ∧
      Fin15AnchoredAtom0824 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0866 chi ∧
      Fin15AnchoredAtom0921 chi ∧
      Fin15AnchoredAtom1141 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0824 Fin15AnchoredAtom0826 Fin15AnchoredAtom0866
    Fin15AnchoredAtom0921 Fin15AnchoredAtom1141 Fin15AnchoredAtom2857 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01294
  ] at hbad
  tauto

theorem fin15Anchored_clause20487 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2859 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom2859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04366
  ] at hbad
  tauto

theorem fin15Anchored_clause20488 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2859 chi ∧
      Fin15AnchoredAtom0824 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0868 chi ∧
      Fin15AnchoredAtom0923 chi ∧
      Fin15AnchoredAtom1143 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0824 Fin15AnchoredAtom0828 Fin15AnchoredAtom0868
    Fin15AnchoredAtom0923 Fin15AnchoredAtom1143 Fin15AnchoredAtom2859 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04366
  ] at hbad
  tauto

theorem fin15Anchored_clause20489 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2860 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom2860 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08462
  ] at hbad
  tauto

theorem fin15Anchored_clause20490 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2861 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2861 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16654
  ] at hbad
  tauto

theorem fin15Anchored_clause20491 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom2862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01550
  ] at hbad
  tauto

theorem fin15Anchored_clause20492 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom2862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01550
  ] at hbad
  tauto

theorem fin15Anchored_clause20493 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom2862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01550
  ] at hbad
  tauto

theorem fin15Anchored_clause20494 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom0926 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0926 Fin15AnchoredAtom2862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01550
  ] at hbad
  tauto

theorem fin15Anchored_clause20495 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2862 chi ∧
      ¬Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1146 Fin15AnchoredAtom2862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01550
  ] at hbad
  tauto

theorem fin15Anchored_clause20496 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2862 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0926 chi ∧
      Fin15AnchoredAtom1146 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom0826 Fin15AnchoredAtom0871
    Fin15AnchoredAtom0926 Fin15AnchoredAtom1146 Fin15AnchoredAtom2862 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01550
  ] at hbad
  tauto

theorem fin15Anchored_clause20497 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2863 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom2863 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02574
  ] at hbad
  tauto

theorem fin15Anchored_clause20498 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom2864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04622
  ] at hbad
  tauto

theorem fin15Anchored_clause20499 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom2864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04622
  ] at hbad
  tauto

theorem fin15Anchored_clause20500 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom2864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04622
  ] at hbad
  tauto

theorem fin15Anchored_clause20501 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom0928 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0928 Fin15AnchoredAtom2864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04622
  ] at hbad
  tauto

theorem fin15Anchored_clause20502 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2864 chi ∧
      ¬Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1148 Fin15AnchoredAtom2864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04622
  ] at hbad
  tauto

theorem fin15Anchored_clause20503 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2864 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0928 chi ∧
      Fin15AnchoredAtom1148 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom0828 Fin15AnchoredAtom0873
    Fin15AnchoredAtom0928 Fin15AnchoredAtom1148 Fin15AnchoredAtom2864 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04622
  ] at hbad
  tauto

theorem fin15Anchored_clause20504 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom2865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08718
  ] at hbad
  tauto

theorem fin15Anchored_clause20505 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom2865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08718
  ] at hbad
  tauto

theorem fin15Anchored_clause20506 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom2865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08718
  ] at hbad
  tauto

theorem fin15Anchored_clause20507 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom0929 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0929 Fin15AnchoredAtom2865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08718
  ] at hbad
  tauto

theorem fin15Anchored_clause20508 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2865 chi ∧
      ¬Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1149 Fin15AnchoredAtom2865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08718
  ] at hbad
  tauto

theorem fin15Anchored_clause20509 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2865 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0929 chi ∧
      Fin15AnchoredAtom1149 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom0829 Fin15AnchoredAtom0874
    Fin15AnchoredAtom0929 Fin15AnchoredAtom1149 Fin15AnchoredAtom2865 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08718
  ] at hbad
  tauto

theorem fin15Anchored_clause20510 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom0825 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom2866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16910
  ] at hbad
  tauto

theorem fin15Anchored_clause20511 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16910
  ] at hbad
  tauto

theorem fin15Anchored_clause20512 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0875 Fin15AnchoredAtom2866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16910
  ] at hbad
  tauto

theorem fin15Anchored_clause20513 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom0930 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0930 Fin15AnchoredAtom2866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16910
  ] at hbad
  tauto

theorem fin15Anchored_clause20514 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2866 chi ∧
      ¬Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1150 Fin15AnchoredAtom2866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16910
  ] at hbad
  tauto

theorem fin15Anchored_clause20515 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2866 chi ∧
      Fin15AnchoredAtom0825 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0930 chi ∧
      Fin15AnchoredAtom1150 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0825 Fin15AnchoredAtom0830 Fin15AnchoredAtom0875
    Fin15AnchoredAtom0930 Fin15AnchoredAtom1150 Fin15AnchoredAtom2866 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16910
  ] at hbad
  tauto

theorem fin15Anchored_clause20516 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2867 chi ∧
      ¬Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1151 Fin15AnchoredAtom2867 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03086
  ] at hbad
  tauto

theorem fin15Anchored_clause20517 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2867 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom0931 chi ∧
      Fin15AnchoredAtom1151 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom0827 Fin15AnchoredAtom0876
    Fin15AnchoredAtom0931 Fin15AnchoredAtom1151 Fin15AnchoredAtom2867 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03086
  ] at hbad
  tauto

theorem fin15Anchored_clause20518 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom2868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05134
  ] at hbad
  tauto

theorem fin15Anchored_clause20519 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom2868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05134
  ] at hbad
  tauto

theorem fin15Anchored_clause20520 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom2868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05134
  ] at hbad
  tauto

theorem fin15Anchored_clause20521 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom0932 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0932 Fin15AnchoredAtom2868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05134
  ] at hbad
  tauto

theorem fin15Anchored_clause20522 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2868 chi ∧
      ¬Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1152 Fin15AnchoredAtom2868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05134
  ] at hbad
  tauto

theorem fin15Anchored_clause20523 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2868 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0932 chi ∧
      Fin15AnchoredAtom1152 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom0828 Fin15AnchoredAtom0877
    Fin15AnchoredAtom0932 Fin15AnchoredAtom1152 Fin15AnchoredAtom2868 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05134
  ] at hbad
  tauto

theorem fin15Anchored_clause20524 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom2869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09230
  ] at hbad
  tauto

theorem fin15Anchored_clause20525 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom2869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09230
  ] at hbad
  tauto

theorem fin15Anchored_clause20526 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom2869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09230
  ] at hbad
  tauto

theorem fin15Anchored_clause20527 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom0933 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0933 Fin15AnchoredAtom2869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09230
  ] at hbad
  tauto

theorem fin15Anchored_clause20528 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2869 chi ∧
      ¬Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1153 Fin15AnchoredAtom2869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09230
  ] at hbad
  tauto

theorem fin15Anchored_clause20529 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2869 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom0933 chi ∧
      Fin15AnchoredAtom1153 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom0829 Fin15AnchoredAtom0878
    Fin15AnchoredAtom0933 Fin15AnchoredAtom1153 Fin15AnchoredAtom2869 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09230
  ] at hbad
  tauto

theorem fin15Anchored_clause20530 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom0826 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom2870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17422
  ] at hbad
  tauto

theorem fin15Anchored_clause20531 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17422
  ] at hbad
  tauto

theorem fin15Anchored_clause20532 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0879 Fin15AnchoredAtom2870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17422
  ] at hbad
  tauto

theorem fin15Anchored_clause20533 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom0934 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0934 Fin15AnchoredAtom2870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17422
  ] at hbad
  tauto

theorem fin15Anchored_clause20534 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2870 chi ∧
      ¬Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1154 Fin15AnchoredAtom2870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17422
  ] at hbad
  tauto

theorem fin15Anchored_clause20535 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2870 chi ∧
      Fin15AnchoredAtom0826 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom0934 chi ∧
      Fin15AnchoredAtom1154 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0826 Fin15AnchoredAtom0830 Fin15AnchoredAtom0879
    Fin15AnchoredAtom0934 Fin15AnchoredAtom1154 Fin15AnchoredAtom2870 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17422
  ] at hbad
  tauto

theorem fin15Anchored_clause20536 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2872 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0881 chi ∧
      Fin15AnchoredAtom0936 chi ∧
      Fin15AnchoredAtom1156 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0827 Fin15AnchoredAtom0829 Fin15AnchoredAtom0881
    Fin15AnchoredAtom0936 Fin15AnchoredAtom1156 Fin15AnchoredAtom2872 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10254
  ] at hbad
  tauto

theorem fin15Anchored_clause20537 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2873 chi ∧
      ¬Fin15AnchoredAtom0827 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0827 Fin15AnchoredAtom2873 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18446
  ] at hbad
  tauto

theorem fin15Anchored_clause20538 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2873 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2873 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18446
  ] at hbad
  tauto

theorem fin15Anchored_clause20539 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2873 chi ∧
      ¬Fin15AnchoredAtom0882 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0882 Fin15AnchoredAtom2873 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18446
  ] at hbad
  tauto

theorem fin15Anchored_clause20540 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2873 chi ∧
      Fin15AnchoredAtom0827 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0882 chi ∧
      Fin15AnchoredAtom0937 chi ∧
      Fin15AnchoredAtom1157 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0827 Fin15AnchoredAtom0830 Fin15AnchoredAtom0882
    Fin15AnchoredAtom0937 Fin15AnchoredAtom1157 Fin15AnchoredAtom2873 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18446
  ] at hbad
  tauto

theorem fin15Anchored_clause20541 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom2874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12302
  ] at hbad
  tauto

theorem fin15Anchored_clause20542 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom2874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12302
  ] at hbad
  tauto

theorem fin15Anchored_clause20543 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom0883 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0883 Fin15AnchoredAtom2874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12302
  ] at hbad
  tauto

theorem fin15Anchored_clause20544 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom0938 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0938 Fin15AnchoredAtom2874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12302
  ] at hbad
  tauto

theorem fin15Anchored_clause20545 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2874 chi ∧
      ¬Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1158 Fin15AnchoredAtom2874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12302
  ] at hbad
  tauto

theorem fin15Anchored_clause20546 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2874 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0883 chi ∧
      Fin15AnchoredAtom0938 chi ∧
      Fin15AnchoredAtom1158 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom0829 Fin15AnchoredAtom0883
    Fin15AnchoredAtom0938 Fin15AnchoredAtom1158 Fin15AnchoredAtom2874 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12302
  ] at hbad
  tauto

theorem fin15Anchored_clause20547 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom0828 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom2875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20494
  ] at hbad
  tauto

theorem fin15Anchored_clause20548 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20494
  ] at hbad
  tauto

theorem fin15Anchored_clause20549 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom0884 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0884 Fin15AnchoredAtom2875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20494
  ] at hbad
  tauto

theorem fin15Anchored_clause20550 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom0939 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0939 Fin15AnchoredAtom2875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20494
  ] at hbad
  tauto

theorem fin15Anchored_clause20551 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2875 chi ∧
      ¬Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1159 Fin15AnchoredAtom2875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20494
  ] at hbad
  tauto

theorem fin15Anchored_clause20552 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2875 chi ∧
      Fin15AnchoredAtom0828 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0884 chi ∧
      Fin15AnchoredAtom0939 chi ∧
      Fin15AnchoredAtom1159 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0828 Fin15AnchoredAtom0830 Fin15AnchoredAtom0884
    Fin15AnchoredAtom0939 Fin15AnchoredAtom1159 Fin15AnchoredAtom2875 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20494
  ] at hbad
  tauto

theorem fin15Anchored_clause20553 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom0829 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom2876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24590
  ] at hbad
  tauto

theorem fin15Anchored_clause20554 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom0830 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0830 Fin15AnchoredAtom2876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24590
  ] at hbad
  tauto

theorem fin15Anchored_clause20555 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom0885 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0885 Fin15AnchoredAtom2876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24590
  ] at hbad
  tauto

theorem fin15Anchored_clause20556 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom0940 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0940 Fin15AnchoredAtom2876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24590
  ] at hbad
  tauto

theorem fin15Anchored_clause20557 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2876 chi ∧
      ¬Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1160 Fin15AnchoredAtom2876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24590
  ] at hbad
  tauto

theorem fin15Anchored_clause20558 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2876 chi ∧
      Fin15AnchoredAtom0829 chi ∧
      Fin15AnchoredAtom0830 chi ∧
      Fin15AnchoredAtom0885 chi ∧
      Fin15AnchoredAtom0940 chi ∧
      Fin15AnchoredAtom1160 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0829 Fin15AnchoredAtom0830 Fin15AnchoredAtom0885
    Fin15AnchoredAtom0940 Fin15AnchoredAtom1160 Fin15AnchoredAtom2876 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask24590
  ] at hbad
  tauto

theorem fin15Anchored_clause20559 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom2877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00118
  ] at hbad
  tauto

theorem fin15Anchored_clause20560 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom2877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00118
  ] at hbad
  tauto

theorem fin15Anchored_clause20561 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom0841 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0841 Fin15AnchoredAtom2877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00118
  ] at hbad
  tauto

theorem fin15Anchored_clause20562 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom0941 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0941 Fin15AnchoredAtom2877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00118
  ] at hbad
  tauto

theorem fin15Anchored_clause20563 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2877 chi ∧
      ¬Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1161 Fin15AnchoredAtom2877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00118
  ] at hbad
  tauto

theorem fin15Anchored_clause20564 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2877 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0841 chi ∧
      Fin15AnchoredAtom0941 chi ∧
      Fin15AnchoredAtom1161 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom0832 Fin15AnchoredAtom0841
    Fin15AnchoredAtom0941 Fin15AnchoredAtom1161 Fin15AnchoredAtom2877 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00118
  ] at hbad
  tauto

theorem fin15Anchored_clause20565 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom2878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00182
  ] at hbad
  tauto

theorem fin15Anchored_clause20566 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00182
  ] at hbad
  tauto

theorem fin15Anchored_clause20567 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom0842 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0842 Fin15AnchoredAtom2878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00182
  ] at hbad
  tauto

theorem fin15Anchored_clause20568 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom0942 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0942 Fin15AnchoredAtom2878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00182
  ] at hbad
  tauto

theorem fin15Anchored_clause20569 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2878 chi ∧
      ¬Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1162 Fin15AnchoredAtom2878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00182
  ] at hbad
  tauto

theorem fin15Anchored_clause20570 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2878 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0842 chi ∧
      Fin15AnchoredAtom0942 chi ∧
      Fin15AnchoredAtom1162 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom0833 Fin15AnchoredAtom0842
    Fin15AnchoredAtom0942 Fin15AnchoredAtom1162 Fin15AnchoredAtom2878 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00182
  ] at hbad
  tauto

theorem fin15Anchored_clause20571 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom2880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00566
  ] at hbad
  tauto

theorem fin15Anchored_clause20572 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom2880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00566
  ] at hbad
  tauto

theorem fin15Anchored_clause20573 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom0844 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0844 Fin15AnchoredAtom2880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00566
  ] at hbad
  tauto

theorem fin15Anchored_clause20574 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom0944 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0944 Fin15AnchoredAtom2880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00566
  ] at hbad
  tauto

theorem fin15Anchored_clause20575 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2880 chi ∧
      ¬Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1164 Fin15AnchoredAtom2880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00566
  ] at hbad
  tauto

theorem fin15Anchored_clause20576 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2880 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0844 chi ∧
      Fin15AnchoredAtom0944 chi ∧
      Fin15AnchoredAtom1164 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom0835 Fin15AnchoredAtom0844
    Fin15AnchoredAtom0944 Fin15AnchoredAtom1164 Fin15AnchoredAtom2880 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00566
  ] at hbad
  tauto

theorem fin15Anchored_clause20577 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom2881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01078
  ] at hbad
  tauto

theorem fin15Anchored_clause20578 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom2881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01078
  ] at hbad
  tauto

theorem fin15Anchored_clause20579 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom0845 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0845 Fin15AnchoredAtom2881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01078
  ] at hbad
  tauto

theorem fin15Anchored_clause20580 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom0945 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0945 Fin15AnchoredAtom2881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01078
  ] at hbad
  tauto

theorem fin15Anchored_clause20581 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2881 chi ∧
      ¬Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1165 Fin15AnchoredAtom2881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01078
  ] at hbad
  tauto

theorem fin15Anchored_clause20582 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2881 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0845 chi ∧
      Fin15AnchoredAtom0945 chi ∧
      Fin15AnchoredAtom1165 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom0836 Fin15AnchoredAtom0845
    Fin15AnchoredAtom0945 Fin15AnchoredAtom1165 Fin15AnchoredAtom2881 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01078
  ] at hbad
  tauto

theorem fin15Anchored_clause20583 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom2882 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02102
  ] at hbad
  tauto

theorem fin15Anchored_clause20584 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom0846 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0846 Fin15AnchoredAtom2882 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02102
  ] at hbad
  tauto

theorem fin15Anchored_clause20585 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom0946 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0946 Fin15AnchoredAtom2882 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02102
  ] at hbad
  tauto

theorem fin15Anchored_clause20586 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2882 chi ∧
      ¬Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1166 Fin15AnchoredAtom2882 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02102
  ] at hbad
  tauto

theorem fin15Anchored_clause20587 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2882 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0846 chi ∧
      Fin15AnchoredAtom0946 chi ∧
      Fin15AnchoredAtom1166 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom0837 Fin15AnchoredAtom0846
    Fin15AnchoredAtom0946 Fin15AnchoredAtom1166 Fin15AnchoredAtom2882 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02102
  ] at hbad
  tauto

theorem fin15Anchored_clause20588 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom2883 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04150
  ] at hbad
  tauto

theorem fin15Anchored_clause20589 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom2883 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04150
  ] at hbad
  tauto

theorem fin15Anchored_clause20590 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom0847 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0847 Fin15AnchoredAtom2883 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04150
  ] at hbad
  tauto

theorem fin15Anchored_clause20591 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom0947 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0947 Fin15AnchoredAtom2883 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04150
  ] at hbad
  tauto

theorem fin15Anchored_clause20592 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2883 chi ∧
      ¬Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1167 Fin15AnchoredAtom2883 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04150
  ] at hbad
  tauto

theorem fin15Anchored_clause20593 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2883 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0847 chi ∧
      Fin15AnchoredAtom0947 chi ∧
      Fin15AnchoredAtom1167 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom0838 Fin15AnchoredAtom0847
    Fin15AnchoredAtom0947 Fin15AnchoredAtom1167 Fin15AnchoredAtom2883 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04150
  ] at hbad
  tauto

theorem fin15Anchored_clause20594 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom2884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08246
  ] at hbad
  tauto

theorem fin15Anchored_clause20595 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom2884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08246
  ] at hbad
  tauto

theorem fin15Anchored_clause20596 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom0848 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0848 Fin15AnchoredAtom2884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08246
  ] at hbad
  tauto

theorem fin15Anchored_clause20597 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom0948 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0948 Fin15AnchoredAtom2884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08246
  ] at hbad
  tauto

theorem fin15Anchored_clause20598 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2884 chi ∧
      ¬Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1168 Fin15AnchoredAtom2884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08246
  ] at hbad
  tauto

theorem fin15Anchored_clause20599 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2884 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0848 chi ∧
      Fin15AnchoredAtom0948 chi ∧
      Fin15AnchoredAtom1168 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom0839 Fin15AnchoredAtom0848
    Fin15AnchoredAtom0948 Fin15AnchoredAtom1168 Fin15AnchoredAtom2884 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08246
  ] at hbad
  tauto

theorem fin15Anchored_clause20600 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom0831 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom2885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16438
  ] at hbad
  tauto

theorem fin15Anchored_clause20601 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom2885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16438
  ] at hbad
  tauto

theorem fin15Anchored_clause20602 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom0849 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0849 Fin15AnchoredAtom2885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16438
  ] at hbad
  tauto

theorem fin15Anchored_clause20603 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom0949 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0949 Fin15AnchoredAtom2885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16438
  ] at hbad
  tauto

theorem fin15Anchored_clause20604 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2885 chi ∧
      ¬Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1169 Fin15AnchoredAtom2885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16438
  ] at hbad
  tauto

theorem fin15Anchored_clause20605 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2885 chi ∧
      Fin15AnchoredAtom0831 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0849 chi ∧
      Fin15AnchoredAtom0949 chi ∧
      Fin15AnchoredAtom1169 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0831 Fin15AnchoredAtom0840 Fin15AnchoredAtom0849
    Fin15AnchoredAtom0949 Fin15AnchoredAtom1169 Fin15AnchoredAtom2885 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16438
  ] at hbad
  tauto

theorem fin15Anchored_clause20606 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom2886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00214
  ] at hbad
  tauto

theorem fin15Anchored_clause20607 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00214
  ] at hbad
  tauto

end ErdosSzekeres

end
