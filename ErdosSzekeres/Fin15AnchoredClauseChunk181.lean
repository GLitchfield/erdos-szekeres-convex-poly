module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 181. -/

theorem fin15Anchored_clause23168 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom3495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13442
  ] at hbad
  tauto

theorem fin15Anchored_clause23169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13442
  ] at hbad
  tauto

theorem fin15Anchored_clause23170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13442
  ] at hbad
  tauto

theorem fin15Anchored_clause23171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3495 chi ∧
      ¬Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1779 Fin15AnchoredAtom3495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13442
  ] at hbad
  tauto

theorem fin15Anchored_clause23172 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3495 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1779 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom1063 Fin15AnchoredAtom1068
    Fin15AnchoredAtom1099 Fin15AnchoredAtom1779 Fin15AnchoredAtom3495 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13442
  ] at hbad
  tauto

theorem fin15Anchored_clause23173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1062 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom3496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21634
  ] at hbad
  tauto

theorem fin15Anchored_clause23174 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21634
  ] at hbad
  tauto

theorem fin15Anchored_clause23175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21634
  ] at hbad
  tauto

theorem fin15Anchored_clause23176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21634
  ] at hbad
  tauto

theorem fin15Anchored_clause23177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3496 chi ∧
      ¬Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1780 Fin15AnchoredAtom3496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21634
  ] at hbad
  tauto

theorem fin15Anchored_clause23178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3496 chi ∧
      Fin15AnchoredAtom1062 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1780 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1062 Fin15AnchoredAtom1064 Fin15AnchoredAtom1069
    Fin15AnchoredAtom1100 Fin15AnchoredAtom1780 Fin15AnchoredAtom3496 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21634
  ] at hbad
  tauto

theorem fin15Anchored_clause23179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1063 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom3497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25730
  ] at hbad
  tauto

theorem fin15Anchored_clause23180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1064 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1064 Fin15AnchoredAtom3497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25730
  ] at hbad
  tauto

theorem fin15Anchored_clause23181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25730
  ] at hbad
  tauto

theorem fin15Anchored_clause23182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25730
  ] at hbad
  tauto

theorem fin15Anchored_clause23183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3497 chi ∧
      ¬Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1781 Fin15AnchoredAtom3497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25730
  ] at hbad
  tauto

theorem fin15Anchored_clause23184 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3497 chi ∧
      Fin15AnchoredAtom1063 chi ∧
      Fin15AnchoredAtom1064 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1781 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1063 Fin15AnchoredAtom1064 Fin15AnchoredAtom1070
    Fin15AnchoredAtom1101 Fin15AnchoredAtom1781 Fin15AnchoredAtom3497 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25730
  ] at hbad
  tauto

theorem fin15Anchored_clause23185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3498 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14466
  ] at hbad
  tauto

theorem fin15Anchored_clause23186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3498 chi ∧
      ¬Fin15AnchoredAtom1782 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1782 Fin15AnchoredAtom3498 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14466
  ] at hbad
  tauto

theorem fin15Anchored_clause23187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3499 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3499 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22658
  ] at hbad
  tauto

theorem fin15Anchored_clause23188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3500 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3500 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26754
  ] at hbad
  tauto

theorem fin15Anchored_clause23189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1068 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom3501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28802
  ] at hbad
  tauto

theorem fin15Anchored_clause23190 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1069 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1069 Fin15AnchoredAtom3501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28802
  ] at hbad
  tauto

theorem fin15Anchored_clause23191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1070 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1070 Fin15AnchoredAtom3501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28802
  ] at hbad
  tauto

theorem fin15Anchored_clause23192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28802
  ] at hbad
  tauto

theorem fin15Anchored_clause23193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3501 chi ∧
      ¬Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1785 Fin15AnchoredAtom3501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28802
  ] at hbad
  tauto

theorem fin15Anchored_clause23194 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3501 chi ∧
      Fin15AnchoredAtom1068 chi ∧
      Fin15AnchoredAtom1069 chi ∧
      Fin15AnchoredAtom1070 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1785 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1068 Fin15AnchoredAtom1069 Fin15AnchoredAtom1070
    Fin15AnchoredAtom1105 Fin15AnchoredAtom1785 Fin15AnchoredAtom3501 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28802
  ] at hbad
  tauto

theorem fin15Anchored_clause23195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom3503 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05890
  ] at hbad
  tauto

theorem fin15Anchored_clause23196 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom3503 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05890
  ] at hbad
  tauto

theorem fin15Anchored_clause23197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1077 Fin15AnchoredAtom3503 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05890
  ] at hbad
  tauto

theorem fin15Anchored_clause23198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3503 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05890
  ] at hbad
  tauto

theorem fin15Anchored_clause23199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3503 chi ∧
      ¬Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1787 Fin15AnchoredAtom3503 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05890
  ] at hbad
  tauto

theorem fin15Anchored_clause23200 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3503 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1787 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom1073 Fin15AnchoredAtom1077
    Fin15AnchoredAtom1087 Fin15AnchoredAtom1787 Fin15AnchoredAtom3503 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05890
  ] at hbad
  tauto

theorem fin15Anchored_clause23201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom3504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09986
  ] at hbad
  tauto

theorem fin15Anchored_clause23202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1074 Fin15AnchoredAtom3504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09986
  ] at hbad
  tauto

theorem fin15Anchored_clause23203 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom3504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09986
  ] at hbad
  tauto

theorem fin15Anchored_clause23204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09986
  ] at hbad
  tauto

theorem fin15Anchored_clause23205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3504 chi ∧
      ¬Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1788 Fin15AnchoredAtom3504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09986
  ] at hbad
  tauto

theorem fin15Anchored_clause23206 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3504 chi ∧
      Fin15AnchoredAtom1071 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1788 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom1074 Fin15AnchoredAtom1078
    Fin15AnchoredAtom1088 Fin15AnchoredAtom1788 Fin15AnchoredAtom3504 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09986
  ] at hbad
  tauto

theorem fin15Anchored_clause23207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1071 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1071 Fin15AnchoredAtom3505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18178
  ] at hbad
  tauto

theorem fin15Anchored_clause23208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1075 Fin15AnchoredAtom3505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18178
  ] at hbad
  tauto

theorem fin15Anchored_clause23209 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1079 Fin15AnchoredAtom3505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18178
  ] at hbad
  tauto

theorem fin15Anchored_clause23210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom3505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18178
  ] at hbad
  tauto

theorem fin15Anchored_clause23211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3505 chi ∧
      ¬Fin15AnchoredAtom1789 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1789 Fin15AnchoredAtom3505 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18178
  ] at hbad
  tauto

theorem fin15Anchored_clause23212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom3509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13058
  ] at hbad
  tauto

theorem fin15Anchored_clause23213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1074 Fin15AnchoredAtom3509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13058
  ] at hbad
  tauto

theorem fin15Anchored_clause23214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1083 Fin15AnchoredAtom3509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13058
  ] at hbad
  tauto

theorem fin15Anchored_clause23215 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13058
  ] at hbad
  tauto

theorem fin15Anchored_clause23216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3509 chi ∧
      ¬Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1793 Fin15AnchoredAtom3509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13058
  ] at hbad
  tauto

theorem fin15Anchored_clause23217 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3509 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1074 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1793 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom1074 Fin15AnchoredAtom1083
    Fin15AnchoredAtom1093 Fin15AnchoredAtom1793 Fin15AnchoredAtom3509 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13058
  ] at hbad
  tauto

theorem fin15Anchored_clause23218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom1073 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom3510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21250
  ] at hbad
  tauto

theorem fin15Anchored_clause23219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1075 Fin15AnchoredAtom3510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21250
  ] at hbad
  tauto

theorem fin15Anchored_clause23220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21250
  ] at hbad
  tauto

theorem fin15Anchored_clause23221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3510 chi ∧
      ¬Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1794 Fin15AnchoredAtom3510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21250
  ] at hbad
  tauto

theorem fin15Anchored_clause23222 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3510 chi ∧
      Fin15AnchoredAtom1073 chi ∧
      Fin15AnchoredAtom1075 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1794 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1073 Fin15AnchoredAtom1075 Fin15AnchoredAtom1084
    Fin15AnchoredAtom1094 Fin15AnchoredAtom1794 Fin15AnchoredAtom3510 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21250
  ] at hbad
  tauto

theorem fin15Anchored_clause23223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1074 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1074 Fin15AnchoredAtom3511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25346
  ] at hbad
  tauto

theorem fin15Anchored_clause23224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1075 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1075 Fin15AnchoredAtom3511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25346
  ] at hbad
  tauto

theorem fin15Anchored_clause23225 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1085 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1085 Fin15AnchoredAtom3511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25346
  ] at hbad
  tauto

theorem fin15Anchored_clause23226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom3511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25346
  ] at hbad
  tauto

theorem fin15Anchored_clause23227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3511 chi ∧
      ¬Fin15AnchoredAtom1795 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1795 Fin15AnchoredAtom3511 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25346
  ] at hbad
  tauto

theorem fin15Anchored_clause23228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1077 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1077 Fin15AnchoredAtom3515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13570
  ] at hbad
  tauto

theorem fin15Anchored_clause23229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom3515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13570
  ] at hbad
  tauto

theorem fin15Anchored_clause23230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1083 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1083 Fin15AnchoredAtom3515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13570
  ] at hbad
  tauto

theorem fin15Anchored_clause23231 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13570
  ] at hbad
  tauto

theorem fin15Anchored_clause23232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3515 chi ∧
      ¬Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1799 Fin15AnchoredAtom3515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13570
  ] at hbad
  tauto

theorem fin15Anchored_clause23233 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3515 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1799 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1077 Fin15AnchoredAtom1078 Fin15AnchoredAtom1083
    Fin15AnchoredAtom1099 Fin15AnchoredAtom1799 Fin15AnchoredAtom3515 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13570
  ] at hbad
  tauto

theorem fin15Anchored_clause23234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1079 Fin15AnchoredAtom3516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21762
  ] at hbad
  tauto

theorem fin15Anchored_clause23235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21762
  ] at hbad
  tauto

theorem fin15Anchored_clause23236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3516 chi ∧
      ¬Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1800 Fin15AnchoredAtom3516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21762
  ] at hbad
  tauto

theorem fin15Anchored_clause23237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3516 chi ∧
      Fin15AnchoredAtom1077 chi ∧
      Fin15AnchoredAtom1079 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1800 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1077 Fin15AnchoredAtom1079 Fin15AnchoredAtom1084
    Fin15AnchoredAtom1100 Fin15AnchoredAtom1800 Fin15AnchoredAtom3516 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask21762
  ] at hbad
  tauto

theorem fin15Anchored_clause23238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom1078 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom3517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25858
  ] at hbad
  tauto

theorem fin15Anchored_clause23239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom1079 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1079 Fin15AnchoredAtom3517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25858
  ] at hbad
  tauto

theorem fin15Anchored_clause23240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25858
  ] at hbad
  tauto

theorem fin15Anchored_clause23241 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3517 chi ∧
      ¬Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1801 Fin15AnchoredAtom3517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25858
  ] at hbad
  tauto

theorem fin15Anchored_clause23242 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3517 chi ∧
      Fin15AnchoredAtom1078 chi ∧
      Fin15AnchoredAtom1079 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1801 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1078 Fin15AnchoredAtom1079 Fin15AnchoredAtom1085
    Fin15AnchoredAtom1101 Fin15AnchoredAtom1801 Fin15AnchoredAtom3517 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask25858
  ] at hbad
  tauto

theorem fin15Anchored_clause23243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom1084 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1084 Fin15AnchoredAtom3521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28930
  ] at hbad
  tauto

theorem fin15Anchored_clause23244 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28930
  ] at hbad
  tauto

theorem fin15Anchored_clause23245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3521 chi ∧
      ¬Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1805 Fin15AnchoredAtom3521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28930
  ] at hbad
  tauto

theorem fin15Anchored_clause23246 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3521 chi ∧
      Fin15AnchoredAtom1083 chi ∧
      Fin15AnchoredAtom1084 chi ∧
      Fin15AnchoredAtom1085 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1805 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1083 Fin15AnchoredAtom1084 Fin15AnchoredAtom1085
    Fin15AnchoredAtom1105 Fin15AnchoredAtom1805 Fin15AnchoredAtom3521 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask28930
  ] at hbad
  tauto

theorem fin15Anchored_clause23247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom1086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1086 Fin15AnchoredAtom3522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07682
  ] at hbad
  tauto

theorem fin15Anchored_clause23248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07682
  ] at hbad
  tauto

theorem fin15Anchored_clause23249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom1096 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1096 Fin15AnchoredAtom3522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07682
  ] at hbad
  tauto

theorem fin15Anchored_clause23250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3522 chi ∧
      ¬Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1806 Fin15AnchoredAtom3522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07682
  ] at hbad
  tauto

theorem fin15Anchored_clause23251 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3522 chi ∧
      Fin15AnchoredAtom1086 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1090 chi ∧
      Fin15AnchoredAtom1096 chi ∧
      Fin15AnchoredAtom1806 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1086 Fin15AnchoredAtom1087 Fin15AnchoredAtom1090
    Fin15AnchoredAtom1096 Fin15AnchoredAtom1806 Fin15AnchoredAtom3522 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask07682
  ] at hbad
  tauto

theorem fin15Anchored_clause23252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3523 chi ∧
      ¬Fin15AnchoredAtom1086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1086 Fin15AnchoredAtom3523 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11778
  ] at hbad
  tauto

theorem fin15Anchored_clause23253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3523 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3523 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask11778
  ] at hbad
  tauto

theorem fin15Anchored_clause23254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3524 chi ∧
      ¬Fin15AnchoredAtom1086 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1086 Fin15AnchoredAtom3524 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask19970
  ] at hbad
  tauto

theorem fin15Anchored_clause23255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13826
  ] at hbad
  tauto

theorem fin15Anchored_clause23256 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13826
  ] at hbad
  tauto

theorem fin15Anchored_clause23257 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13826
  ] at hbad
  tauto

theorem fin15Anchored_clause23258 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13826
  ] at hbad
  tauto

theorem fin15Anchored_clause23259 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3525 chi ∧
      ¬Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1809 Fin15AnchoredAtom3525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13826
  ] at hbad
  tauto

theorem fin15Anchored_clause23260 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3525 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1809 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom1088 Fin15AnchoredAtom1093
    Fin15AnchoredAtom1099 Fin15AnchoredAtom1809 Fin15AnchoredAtom3525 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask13826
  ] at hbad
  tauto

theorem fin15Anchored_clause23261 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1087 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom3526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22018
  ] at hbad
  tauto

theorem fin15Anchored_clause23262 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom3526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22018
  ] at hbad
  tauto

theorem fin15Anchored_clause23263 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22018
  ] at hbad
  tauto

theorem fin15Anchored_clause23264 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22018
  ] at hbad
  tauto

theorem fin15Anchored_clause23265 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3526 chi ∧
      ¬Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1810 Fin15AnchoredAtom3526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22018
  ] at hbad
  tauto

theorem fin15Anchored_clause23266 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3526 chi ∧
      Fin15AnchoredAtom1087 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1810 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1087 Fin15AnchoredAtom1089 Fin15AnchoredAtom1094
    Fin15AnchoredAtom1100 Fin15AnchoredAtom1810 Fin15AnchoredAtom3526 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask22018
  ] at hbad
  tauto

theorem fin15Anchored_clause23267 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1088 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom3527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26114
  ] at hbad
  tauto

theorem fin15Anchored_clause23268 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1089 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1089 Fin15AnchoredAtom3527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26114
  ] at hbad
  tauto

theorem fin15Anchored_clause23269 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom3527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26114
  ] at hbad
  tauto

theorem fin15Anchored_clause23270 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26114
  ] at hbad
  tauto

theorem fin15Anchored_clause23271 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3527 chi ∧
      ¬Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1811 Fin15AnchoredAtom3527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26114
  ] at hbad
  tauto

theorem fin15Anchored_clause23272 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3527 chi ∧
      Fin15AnchoredAtom1088 chi ∧
      Fin15AnchoredAtom1089 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1811 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1088 Fin15AnchoredAtom1089 Fin15AnchoredAtom1095
    Fin15AnchoredAtom1101 Fin15AnchoredAtom1811 Fin15AnchoredAtom3527 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask26114
  ] at hbad
  tauto

theorem fin15Anchored_clause23273 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3528 chi ∧
      ¬Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1090 Fin15AnchoredAtom3528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14850
  ] at hbad
  tauto

theorem fin15Anchored_clause23274 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3528 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3528 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask14850
  ] at hbad
  tauto

theorem fin15Anchored_clause23275 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom1090 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1090 Fin15AnchoredAtom3529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23042
  ] at hbad
  tauto

theorem fin15Anchored_clause23276 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23042
  ] at hbad
  tauto

theorem fin15Anchored_clause23277 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3529 chi ∧
      ¬Fin15AnchoredAtom1103 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1103 Fin15AnchoredAtom3529 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23042
  ] at hbad
  tauto

theorem fin15Anchored_clause23278 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1093 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom3531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29186
  ] at hbad
  tauto

theorem fin15Anchored_clause23279 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1094 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1094 Fin15AnchoredAtom3531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29186
  ] at hbad
  tauto

theorem fin15Anchored_clause23280 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1095 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1095 Fin15AnchoredAtom3531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29186
  ] at hbad
  tauto

theorem fin15Anchored_clause23281 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29186
  ] at hbad
  tauto

theorem fin15Anchored_clause23282 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3531 chi ∧
      ¬Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1815 Fin15AnchoredAtom3531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29186
  ] at hbad
  tauto

theorem fin15Anchored_clause23283 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3531 chi ∧
      Fin15AnchoredAtom1093 chi ∧
      Fin15AnchoredAtom1094 chi ∧
      Fin15AnchoredAtom1095 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1815 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1093 Fin15AnchoredAtom1094 Fin15AnchoredAtom1095
    Fin15AnchoredAtom1105 Fin15AnchoredAtom1815 Fin15AnchoredAtom3531 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29186
  ] at hbad
  tauto

theorem fin15Anchored_clause23284 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15362
  ] at hbad
  tauto

theorem fin15Anchored_clause23285 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom1102 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1102 Fin15AnchoredAtom3532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15362
  ] at hbad
  tauto

theorem fin15Anchored_clause23286 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3532 chi ∧
      ¬Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1816 Fin15AnchoredAtom3532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15362
  ] at hbad
  tauto

theorem fin15Anchored_clause23287 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3532 chi ∧
      Fin15AnchoredAtom1096 chi ∧
      Fin15AnchoredAtom1097 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1102 chi ∧
      Fin15AnchoredAtom1816 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1096 Fin15AnchoredAtom1097 Fin15AnchoredAtom1099
    Fin15AnchoredAtom1102 Fin15AnchoredAtom1816 Fin15AnchoredAtom3532 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask15362
  ] at hbad
  tauto

theorem fin15Anchored_clause23288 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3533 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3533 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask23554
  ] at hbad
  tauto

theorem fin15Anchored_clause23289 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3534 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3534 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask27650
  ] at hbad
  tauto

theorem fin15Anchored_clause23290 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1099 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom3535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29698
  ] at hbad
  tauto

theorem fin15Anchored_clause23291 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1100 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1100 Fin15AnchoredAtom3535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29698
  ] at hbad
  tauto

theorem fin15Anchored_clause23292 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1101 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1101 Fin15AnchoredAtom3535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29698
  ] at hbad
  tauto

theorem fin15Anchored_clause23293 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1105 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1105 Fin15AnchoredAtom3535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29698
  ] at hbad
  tauto

theorem fin15Anchored_clause23294 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom3535 chi ∧
      ¬Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1819 Fin15AnchoredAtom3535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29698
  ] at hbad
  tauto

theorem fin15Anchored_clause23295 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom3535 chi ∧
      Fin15AnchoredAtom1099 chi ∧
      Fin15AnchoredAtom1100 chi ∧
      Fin15AnchoredAtom1101 chi ∧
      Fin15AnchoredAtom1105 chi ∧
      Fin15AnchoredAtom1819 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom1099 Fin15AnchoredAtom1100 Fin15AnchoredAtom1101
    Fin15AnchoredAtom1105 Fin15AnchoredAtom1819 Fin15AnchoredAtom3535 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask29698
  ] at hbad
  tauto

end ErdosSzekeres

end
