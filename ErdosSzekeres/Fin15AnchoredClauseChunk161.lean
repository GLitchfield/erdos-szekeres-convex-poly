module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 161. -/

theorem fin15Anchored_clause20608 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom0850 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0850 Fin15AnchoredAtom2886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00214
  ] at hbad
  tauto

theorem fin15Anchored_clause20609 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom0950 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0950 Fin15AnchoredAtom2886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00214
  ] at hbad
  tauto

theorem fin15Anchored_clause20610 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2886 chi ∧
      ¬Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1170 Fin15AnchoredAtom2886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00214
  ] at hbad
  tauto

theorem fin15Anchored_clause20611 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2886 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0850 chi ∧
      Fin15AnchoredAtom0950 chi ∧
      Fin15AnchoredAtom1170 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom0833 Fin15AnchoredAtom0850
    Fin15AnchoredAtom0950 Fin15AnchoredAtom1170 Fin15AnchoredAtom2886 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00214
  ] at hbad
  tauto

theorem fin15Anchored_clause20612 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2887 chi ∧
      ¬Fin15AnchoredAtom0951 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0951 Fin15AnchoredAtom2887 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00342
  ] at hbad
  tauto

theorem fin15Anchored_clause20613 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom2888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00598
  ] at hbad
  tauto

theorem fin15Anchored_clause20614 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom2888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00598
  ] at hbad
  tauto

theorem fin15Anchored_clause20615 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom0852 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0852 Fin15AnchoredAtom2888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00598
  ] at hbad
  tauto

theorem fin15Anchored_clause20616 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom0952 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0952 Fin15AnchoredAtom2888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00598
  ] at hbad
  tauto

theorem fin15Anchored_clause20617 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2888 chi ∧
      ¬Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1172 Fin15AnchoredAtom2888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00598
  ] at hbad
  tauto

theorem fin15Anchored_clause20618 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2888 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0852 chi ∧
      Fin15AnchoredAtom0952 chi ∧
      Fin15AnchoredAtom1172 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom0835 Fin15AnchoredAtom0852
    Fin15AnchoredAtom0952 Fin15AnchoredAtom1172 Fin15AnchoredAtom2888 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00598
  ] at hbad
  tauto

theorem fin15Anchored_clause20619 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom2889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01110
  ] at hbad
  tauto

theorem fin15Anchored_clause20620 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom2889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01110
  ] at hbad
  tauto

theorem fin15Anchored_clause20621 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom0853 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0853 Fin15AnchoredAtom2889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01110
  ] at hbad
  tauto

theorem fin15Anchored_clause20622 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom0953 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0953 Fin15AnchoredAtom2889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01110
  ] at hbad
  tauto

theorem fin15Anchored_clause20623 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2889 chi ∧
      ¬Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1173 Fin15AnchoredAtom2889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01110
  ] at hbad
  tauto

theorem fin15Anchored_clause20624 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2889 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0853 chi ∧
      Fin15AnchoredAtom0953 chi ∧
      Fin15AnchoredAtom1173 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom0836 Fin15AnchoredAtom0853
    Fin15AnchoredAtom0953 Fin15AnchoredAtom1173 Fin15AnchoredAtom2889 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01110
  ] at hbad
  tauto

theorem fin15Anchored_clause20625 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2890 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom2890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02134
  ] at hbad
  tauto

theorem fin15Anchored_clause20626 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2890 chi ∧
      ¬Fin15AnchoredAtom0854 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0854 Fin15AnchoredAtom2890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02134
  ] at hbad
  tauto

theorem fin15Anchored_clause20627 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2890 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0854 chi ∧
      Fin15AnchoredAtom0954 chi ∧
      Fin15AnchoredAtom1174 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom0837 Fin15AnchoredAtom0854
    Fin15AnchoredAtom0954 Fin15AnchoredAtom1174 Fin15AnchoredAtom2890 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02134
  ] at hbad
  tauto

theorem fin15Anchored_clause20628 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom2891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04182
  ] at hbad
  tauto

theorem fin15Anchored_clause20629 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom2891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04182
  ] at hbad
  tauto

theorem fin15Anchored_clause20630 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom0855 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0855 Fin15AnchoredAtom2891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04182
  ] at hbad
  tauto

theorem fin15Anchored_clause20631 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom0955 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0955 Fin15AnchoredAtom2891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04182
  ] at hbad
  tauto

theorem fin15Anchored_clause20632 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2891 chi ∧
      ¬Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1175 Fin15AnchoredAtom2891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04182
  ] at hbad
  tauto

theorem fin15Anchored_clause20633 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2891 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0855 chi ∧
      Fin15AnchoredAtom0955 chi ∧
      Fin15AnchoredAtom1175 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom0838 Fin15AnchoredAtom0855
    Fin15AnchoredAtom0955 Fin15AnchoredAtom1175 Fin15AnchoredAtom2891 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04182
  ] at hbad
  tauto

theorem fin15Anchored_clause20634 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom2892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08278
  ] at hbad
  tauto

theorem fin15Anchored_clause20635 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom2892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08278
  ] at hbad
  tauto

theorem fin15Anchored_clause20636 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom0856 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0856 Fin15AnchoredAtom2892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08278
  ] at hbad
  tauto

theorem fin15Anchored_clause20637 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom0956 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0956 Fin15AnchoredAtom2892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08278
  ] at hbad
  tauto

theorem fin15Anchored_clause20638 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2892 chi ∧
      ¬Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1176 Fin15AnchoredAtom2892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08278
  ] at hbad
  tauto

theorem fin15Anchored_clause20639 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2892 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0856 chi ∧
      Fin15AnchoredAtom0956 chi ∧
      Fin15AnchoredAtom1176 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom0839 Fin15AnchoredAtom0856
    Fin15AnchoredAtom0956 Fin15AnchoredAtom1176 Fin15AnchoredAtom2892 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08278
  ] at hbad
  tauto

theorem fin15Anchored_clause20640 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom0832 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom2893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16470
  ] at hbad
  tauto

theorem fin15Anchored_clause20641 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom2893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16470
  ] at hbad
  tauto

theorem fin15Anchored_clause20642 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom0857 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0857 Fin15AnchoredAtom2893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16470
  ] at hbad
  tauto

theorem fin15Anchored_clause20643 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom0957 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0957 Fin15AnchoredAtom2893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16470
  ] at hbad
  tauto

theorem fin15Anchored_clause20644 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2893 chi ∧
      ¬Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1177 Fin15AnchoredAtom2893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16470
  ] at hbad
  tauto

theorem fin15Anchored_clause20645 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2893 chi ∧
      Fin15AnchoredAtom0832 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0857 chi ∧
      Fin15AnchoredAtom0957 chi ∧
      Fin15AnchoredAtom1177 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0832 Fin15AnchoredAtom0840 Fin15AnchoredAtom0857
    Fin15AnchoredAtom0957 Fin15AnchoredAtom1177 Fin15AnchoredAtom2893 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16470
  ] at hbad
  tauto

theorem fin15Anchored_clause20646 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2894 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2894 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00406
  ] at hbad
  tauto

theorem fin15Anchored_clause20647 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00662
  ] at hbad
  tauto

theorem fin15Anchored_clause20648 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom2895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00662
  ] at hbad
  tauto

theorem fin15Anchored_clause20649 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom0859 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0859 Fin15AnchoredAtom2895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00662
  ] at hbad
  tauto

theorem fin15Anchored_clause20650 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom2895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00662
  ] at hbad
  tauto

theorem fin15Anchored_clause20651 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2895 chi ∧
      ¬Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1179 Fin15AnchoredAtom2895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00662
  ] at hbad
  tauto

theorem fin15Anchored_clause20652 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2895 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0859 chi ∧
      Fin15AnchoredAtom0959 chi ∧
      Fin15AnchoredAtom1179 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom0835 Fin15AnchoredAtom0859
    Fin15AnchoredAtom0959 Fin15AnchoredAtom1179 Fin15AnchoredAtom2895 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00662
  ] at hbad
  tauto

theorem fin15Anchored_clause20653 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01174
  ] at hbad
  tauto

theorem fin15Anchored_clause20654 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom2896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01174
  ] at hbad
  tauto

theorem fin15Anchored_clause20655 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom0860 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0860 Fin15AnchoredAtom2896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01174
  ] at hbad
  tauto

theorem fin15Anchored_clause20656 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom2896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01174
  ] at hbad
  tauto

theorem fin15Anchored_clause20657 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2896 chi ∧
      ¬Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1180 Fin15AnchoredAtom2896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01174
  ] at hbad
  tauto

theorem fin15Anchored_clause20658 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2896 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0860 chi ∧
      Fin15AnchoredAtom0960 chi ∧
      Fin15AnchoredAtom1180 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom0836 Fin15AnchoredAtom0860
    Fin15AnchoredAtom0960 Fin15AnchoredAtom1180 Fin15AnchoredAtom2896 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01174
  ] at hbad
  tauto

theorem fin15Anchored_clause20659 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2897 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02198
  ] at hbad
  tauto

theorem fin15Anchored_clause20660 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2897 chi ∧
      ¬Fin15AnchoredAtom0961 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0961 Fin15AnchoredAtom2897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02198
  ] at hbad
  tauto

theorem fin15Anchored_clause20661 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2897 chi ∧
      ¬Fin15AnchoredAtom1181 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1181 Fin15AnchoredAtom2897 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02198
  ] at hbad
  tauto

theorem fin15Anchored_clause20662 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04246
  ] at hbad
  tauto

theorem fin15Anchored_clause20663 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom2898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04246
  ] at hbad
  tauto

theorem fin15Anchored_clause20664 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom0862 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0862 Fin15AnchoredAtom2898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04246
  ] at hbad
  tauto

theorem fin15Anchored_clause20665 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom2898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04246
  ] at hbad
  tauto

theorem fin15Anchored_clause20666 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2898 chi ∧
      ¬Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1182 Fin15AnchoredAtom2898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04246
  ] at hbad
  tauto

theorem fin15Anchored_clause20667 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2898 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0862 chi ∧
      Fin15AnchoredAtom0962 chi ∧
      Fin15AnchoredAtom1182 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom0838 Fin15AnchoredAtom0862
    Fin15AnchoredAtom0962 Fin15AnchoredAtom1182 Fin15AnchoredAtom2898 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04246
  ] at hbad
  tauto

theorem fin15Anchored_clause20668 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08342
  ] at hbad
  tauto

theorem fin15Anchored_clause20669 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom2899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08342
  ] at hbad
  tauto

theorem fin15Anchored_clause20670 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom0863 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0863 Fin15AnchoredAtom2899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08342
  ] at hbad
  tauto

theorem fin15Anchored_clause20671 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom2899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08342
  ] at hbad
  tauto

theorem fin15Anchored_clause20672 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2899 chi ∧
      ¬Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1183 Fin15AnchoredAtom2899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08342
  ] at hbad
  tauto

theorem fin15Anchored_clause20673 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2899 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0863 chi ∧
      Fin15AnchoredAtom0963 chi ∧
      Fin15AnchoredAtom1183 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom0839 Fin15AnchoredAtom0863
    Fin15AnchoredAtom0963 Fin15AnchoredAtom1183 Fin15AnchoredAtom2899 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08342
  ] at hbad
  tauto

theorem fin15Anchored_clause20674 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom0833 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom2900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16534
  ] at hbad
  tauto

theorem fin15Anchored_clause20675 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom2900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16534
  ] at hbad
  tauto

theorem fin15Anchored_clause20676 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom0864 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0864 Fin15AnchoredAtom2900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16534
  ] at hbad
  tauto

theorem fin15Anchored_clause20677 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom2900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16534
  ] at hbad
  tauto

theorem fin15Anchored_clause20678 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2900 chi ∧
      ¬Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1184 Fin15AnchoredAtom2900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16534
  ] at hbad
  tauto

theorem fin15Anchored_clause20679 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2900 chi ∧
      Fin15AnchoredAtom0833 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0864 chi ∧
      Fin15AnchoredAtom0964 chi ∧
      Fin15AnchoredAtom1184 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0833 Fin15AnchoredAtom0840 Fin15AnchoredAtom0864
    Fin15AnchoredAtom0964 Fin15AnchoredAtom1184 Fin15AnchoredAtom2900 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16534
  ] at hbad
  tauto

theorem fin15Anchored_clause20680 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2901 chi ∧
      Fin15AnchoredAtom0834 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0865 chi ∧
      Fin15AnchoredAtom0965 chi ∧
      Fin15AnchoredAtom1185 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0834 Fin15AnchoredAtom0835 Fin15AnchoredAtom0865
    Fin15AnchoredAtom0965 Fin15AnchoredAtom1185 Fin15AnchoredAtom2901 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00790
  ] at hbad
  tauto

theorem fin15Anchored_clause20681 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2906 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom2906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16662
  ] at hbad
  tauto

theorem fin15Anchored_clause20682 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2906 chi ∧
      Fin15AnchoredAtom0834 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0870 chi ∧
      Fin15AnchoredAtom0970 chi ∧
      Fin15AnchoredAtom1190 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0834 Fin15AnchoredAtom0840 Fin15AnchoredAtom0870
    Fin15AnchoredAtom0970 Fin15AnchoredAtom1190 Fin15AnchoredAtom2906 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16662
  ] at hbad
  tauto

theorem fin15Anchored_clause20683 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom2907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01558
  ] at hbad
  tauto

theorem fin15Anchored_clause20684 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom2907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01558
  ] at hbad
  tauto

theorem fin15Anchored_clause20685 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom0871 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0871 Fin15AnchoredAtom2907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01558
  ] at hbad
  tauto

theorem fin15Anchored_clause20686 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom2907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01558
  ] at hbad
  tauto

theorem fin15Anchored_clause20687 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2907 chi ∧
      ¬Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1191 Fin15AnchoredAtom2907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01558
  ] at hbad
  tauto

theorem fin15Anchored_clause20688 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2907 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0871 chi ∧
      Fin15AnchoredAtom0971 chi ∧
      Fin15AnchoredAtom1191 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom0836 Fin15AnchoredAtom0871
    Fin15AnchoredAtom0971 Fin15AnchoredAtom1191 Fin15AnchoredAtom2907 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01558
  ] at hbad
  tauto

theorem fin15Anchored_clause20689 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2908 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom2908 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02582
  ] at hbad
  tauto

theorem fin15Anchored_clause20690 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2908 chi ∧
      ¬Fin15AnchoredAtom0972 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0972 Fin15AnchoredAtom2908 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02582
  ] at hbad
  tauto

theorem fin15Anchored_clause20691 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2908 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0872 chi ∧
      Fin15AnchoredAtom0972 chi ∧
      Fin15AnchoredAtom1192 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom0837 Fin15AnchoredAtom0872
    Fin15AnchoredAtom0972 Fin15AnchoredAtom1192 Fin15AnchoredAtom2908 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02582
  ] at hbad
  tauto

theorem fin15Anchored_clause20692 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom2909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04630
  ] at hbad
  tauto

theorem fin15Anchored_clause20693 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom2909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04630
  ] at hbad
  tauto

theorem fin15Anchored_clause20694 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom0873 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0873 Fin15AnchoredAtom2909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04630
  ] at hbad
  tauto

theorem fin15Anchored_clause20695 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom2909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04630
  ] at hbad
  tauto

theorem fin15Anchored_clause20696 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2909 chi ∧
      ¬Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1193 Fin15AnchoredAtom2909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04630
  ] at hbad
  tauto

theorem fin15Anchored_clause20697 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2909 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0873 chi ∧
      Fin15AnchoredAtom0973 chi ∧
      Fin15AnchoredAtom1193 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom0838 Fin15AnchoredAtom0873
    Fin15AnchoredAtom0973 Fin15AnchoredAtom1193 Fin15AnchoredAtom2909 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04630
  ] at hbad
  tauto

theorem fin15Anchored_clause20698 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom2910 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08726
  ] at hbad
  tauto

theorem fin15Anchored_clause20699 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom2910 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08726
  ] at hbad
  tauto

theorem fin15Anchored_clause20700 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom0874 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0874 Fin15AnchoredAtom2910 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08726
  ] at hbad
  tauto

theorem fin15Anchored_clause20701 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom2910 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08726
  ] at hbad
  tauto

theorem fin15Anchored_clause20702 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2910 chi ∧
      ¬Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1194 Fin15AnchoredAtom2910 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08726
  ] at hbad
  tauto

theorem fin15Anchored_clause20703 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2910 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0874 chi ∧
      Fin15AnchoredAtom0974 chi ∧
      Fin15AnchoredAtom1194 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom0839 Fin15AnchoredAtom0874
    Fin15AnchoredAtom0974 Fin15AnchoredAtom1194 Fin15AnchoredAtom2910 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08726
  ] at hbad
  tauto

theorem fin15Anchored_clause20704 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom0835 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom2911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16918
  ] at hbad
  tauto

theorem fin15Anchored_clause20705 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom2911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16918
  ] at hbad
  tauto

theorem fin15Anchored_clause20706 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom0875 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0875 Fin15AnchoredAtom2911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16918
  ] at hbad
  tauto

theorem fin15Anchored_clause20707 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom2911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16918
  ] at hbad
  tauto

theorem fin15Anchored_clause20708 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2911 chi ∧
      ¬Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1195 Fin15AnchoredAtom2911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16918
  ] at hbad
  tauto

theorem fin15Anchored_clause20709 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2911 chi ∧
      Fin15AnchoredAtom0835 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0875 chi ∧
      Fin15AnchoredAtom0975 chi ∧
      Fin15AnchoredAtom1195 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0835 Fin15AnchoredAtom0840 Fin15AnchoredAtom0875
    Fin15AnchoredAtom0975 Fin15AnchoredAtom1195 Fin15AnchoredAtom2911 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16918
  ] at hbad
  tauto

theorem fin15Anchored_clause20710 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2912 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom2912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03094
  ] at hbad
  tauto

theorem fin15Anchored_clause20711 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2912 chi ∧
      ¬Fin15AnchoredAtom0837 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0837 Fin15AnchoredAtom2912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03094
  ] at hbad
  tauto

theorem fin15Anchored_clause20712 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2912 chi ∧
      ¬Fin15AnchoredAtom1196 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1196 Fin15AnchoredAtom2912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03094
  ] at hbad
  tauto

theorem fin15Anchored_clause20713 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2912 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0876 chi ∧
      Fin15AnchoredAtom0976 chi ∧
      Fin15AnchoredAtom1196 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom0837 Fin15AnchoredAtom0876
    Fin15AnchoredAtom0976 Fin15AnchoredAtom1196 Fin15AnchoredAtom2912 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03094
  ] at hbad
  tauto

theorem fin15Anchored_clause20714 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom2913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05142
  ] at hbad
  tauto

theorem fin15Anchored_clause20715 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom2913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05142
  ] at hbad
  tauto

theorem fin15Anchored_clause20716 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom0877 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0877 Fin15AnchoredAtom2913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05142
  ] at hbad
  tauto

theorem fin15Anchored_clause20717 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom2913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05142
  ] at hbad
  tauto

theorem fin15Anchored_clause20718 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2913 chi ∧
      ¬Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1197 Fin15AnchoredAtom2913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05142
  ] at hbad
  tauto

theorem fin15Anchored_clause20719 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2913 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0877 chi ∧
      Fin15AnchoredAtom0977 chi ∧
      Fin15AnchoredAtom1197 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom0838 Fin15AnchoredAtom0877
    Fin15AnchoredAtom0977 Fin15AnchoredAtom1197 Fin15AnchoredAtom2913 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05142
  ] at hbad
  tauto

theorem fin15Anchored_clause20720 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom2914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09238
  ] at hbad
  tauto

theorem fin15Anchored_clause20721 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom0839 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0839 Fin15AnchoredAtom2914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09238
  ] at hbad
  tauto

theorem fin15Anchored_clause20722 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom0878 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0878 Fin15AnchoredAtom2914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09238
  ] at hbad
  tauto

theorem fin15Anchored_clause20723 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom2914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09238
  ] at hbad
  tauto

theorem fin15Anchored_clause20724 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2914 chi ∧
      ¬Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1198 Fin15AnchoredAtom2914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09238
  ] at hbad
  tauto

theorem fin15Anchored_clause20725 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2914 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0839 chi ∧
      Fin15AnchoredAtom0878 chi ∧
      Fin15AnchoredAtom0978 chi ∧
      Fin15AnchoredAtom1198 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom0839 Fin15AnchoredAtom0878
    Fin15AnchoredAtom0978 Fin15AnchoredAtom1198 Fin15AnchoredAtom2914 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09238
  ] at hbad
  tauto

theorem fin15Anchored_clause20726 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom0836 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom2915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17430
  ] at hbad
  tauto

theorem fin15Anchored_clause20727 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom0840 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0840 Fin15AnchoredAtom2915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17430
  ] at hbad
  tauto

theorem fin15Anchored_clause20728 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom0879 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0879 Fin15AnchoredAtom2915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17430
  ] at hbad
  tauto

theorem fin15Anchored_clause20729 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom2915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17430
  ] at hbad
  tauto

theorem fin15Anchored_clause20730 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2915 chi ∧
      ¬Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1199 Fin15AnchoredAtom2915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17430
  ] at hbad
  tauto

theorem fin15Anchored_clause20731 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2915 chi ∧
      Fin15AnchoredAtom0836 chi ∧
      Fin15AnchoredAtom0840 chi ∧
      Fin15AnchoredAtom0879 chi ∧
      Fin15AnchoredAtom0979 chi ∧
      Fin15AnchoredAtom1199 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0836 Fin15AnchoredAtom0840 Fin15AnchoredAtom0879
    Fin15AnchoredAtom0979 Fin15AnchoredAtom1199 Fin15AnchoredAtom2915 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17430
  ] at hbad
  tauto

theorem fin15Anchored_clause20732 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2916 chi ∧
      ¬Fin15AnchoredAtom0838 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0838 Fin15AnchoredAtom2916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06166
  ] at hbad
  tauto

theorem fin15Anchored_clause20733 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2916 chi ∧
      ¬Fin15AnchoredAtom0880 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0880 Fin15AnchoredAtom2916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06166
  ] at hbad
  tauto

theorem fin15Anchored_clause20734 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom2916 chi ∧
      Fin15AnchoredAtom0837 chi ∧
      Fin15AnchoredAtom0838 chi ∧
      Fin15AnchoredAtom0880 chi ∧
      Fin15AnchoredAtom0980 chi ∧
      Fin15AnchoredAtom1200 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0837 Fin15AnchoredAtom0838 Fin15AnchoredAtom0880
    Fin15AnchoredAtom0980 Fin15AnchoredAtom1200 Fin15AnchoredAtom2916 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06166
  ] at hbad
  tauto

theorem fin15Anchored_clause20735 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom2917 chi ∧
      ¬Fin15AnchoredAtom0881 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0881 Fin15AnchoredAtom2917 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10262
  ] at hbad
  tauto

end ErdosSzekeres

end
