module

public import ErdosSzekeres.Fin15AnchoredSupport

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErdosSzekeres

/-! Retained anchored Fin15 semantic clauses in bounded group 126. -/

theorem fin15Anchored_clause16128 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom0506 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0506 Fin15AnchoredAtom1959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00403
  ] at hbad
  tauto

theorem fin15Anchored_clause16129 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1959 chi ∧
      ¬Fin15AnchoredAtom0672 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0672 Fin15AnchoredAtom1959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00403
  ] at hbad
  tauto

theorem fin15Anchored_clause16130 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1959 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0506 chi ∧
      Fin15AnchoredAtom0672 chi ∧
      Fin15AnchoredAtom0958 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom0482 Fin15AnchoredAtom0506
    Fin15AnchoredAtom0672 Fin15AnchoredAtom0958 Fin15AnchoredAtom1959 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00403
  ] at hbad
  tauto

theorem fin15Anchored_clause16131 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00659
  ] at hbad
  tauto

theorem fin15Anchored_clause16132 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00659
  ] at hbad
  tauto

theorem fin15Anchored_clause16133 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0507 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0507 Fin15AnchoredAtom1960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00659
  ] at hbad
  tauto

theorem fin15Anchored_clause16134 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0673 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0673 Fin15AnchoredAtom1960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00659
  ] at hbad
  tauto

theorem fin15Anchored_clause16135 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1960 chi ∧
      ¬Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0959 Fin15AnchoredAtom1960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00659
  ] at hbad
  tauto

theorem fin15Anchored_clause16136 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1960 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0507 chi ∧
      Fin15AnchoredAtom0673 chi ∧
      Fin15AnchoredAtom0959 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom0483 Fin15AnchoredAtom0507
    Fin15AnchoredAtom0673 Fin15AnchoredAtom0959 Fin15AnchoredAtom1960 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00659
  ] at hbad
  tauto

theorem fin15Anchored_clause16137 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01171
  ] at hbad
  tauto

theorem fin15Anchored_clause16138 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01171
  ] at hbad
  tauto

theorem fin15Anchored_clause16139 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0508 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0508 Fin15AnchoredAtom1961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01171
  ] at hbad
  tauto

theorem fin15Anchored_clause16140 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0674 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0674 Fin15AnchoredAtom1961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01171
  ] at hbad
  tauto

theorem fin15Anchored_clause16141 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1961 chi ∧
      ¬Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0960 Fin15AnchoredAtom1961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01171
  ] at hbad
  tauto

theorem fin15Anchored_clause16142 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1961 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0508 chi ∧
      Fin15AnchoredAtom0674 chi ∧
      Fin15AnchoredAtom0960 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom0484 Fin15AnchoredAtom0508
    Fin15AnchoredAtom0674 Fin15AnchoredAtom0960 Fin15AnchoredAtom1961 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01171
  ] at hbad
  tauto

theorem fin15Anchored_clause16143 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1962 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02195
  ] at hbad
  tauto

theorem fin15Anchored_clause16144 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1962 chi ∧
      ¬Fin15AnchoredAtom0675 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0675 Fin15AnchoredAtom1962 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02195
  ] at hbad
  tauto

theorem fin15Anchored_clause16145 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04243
  ] at hbad
  tauto

theorem fin15Anchored_clause16146 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04243
  ] at hbad
  tauto

theorem fin15Anchored_clause16147 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0510 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0510 Fin15AnchoredAtom1963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04243
  ] at hbad
  tauto

theorem fin15Anchored_clause16148 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0676 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0676 Fin15AnchoredAtom1963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04243
  ] at hbad
  tauto

theorem fin15Anchored_clause16149 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1963 chi ∧
      ¬Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0962 Fin15AnchoredAtom1963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04243
  ] at hbad
  tauto

theorem fin15Anchored_clause16150 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1963 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0510 chi ∧
      Fin15AnchoredAtom0676 chi ∧
      Fin15AnchoredAtom0962 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom0486 Fin15AnchoredAtom0510
    Fin15AnchoredAtom0676 Fin15AnchoredAtom0962 Fin15AnchoredAtom1963 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04243
  ] at hbad
  tauto

theorem fin15Anchored_clause16151 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08339
  ] at hbad
  tauto

theorem fin15Anchored_clause16152 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08339
  ] at hbad
  tauto

theorem fin15Anchored_clause16153 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0511 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0511 Fin15AnchoredAtom1964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08339
  ] at hbad
  tauto

theorem fin15Anchored_clause16154 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0677 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0677 Fin15AnchoredAtom1964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08339
  ] at hbad
  tauto

theorem fin15Anchored_clause16155 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1964 chi ∧
      ¬Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0963 Fin15AnchoredAtom1964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08339
  ] at hbad
  tauto

theorem fin15Anchored_clause16156 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1964 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0511 chi ∧
      Fin15AnchoredAtom0677 chi ∧
      Fin15AnchoredAtom0963 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom0487 Fin15AnchoredAtom0511
    Fin15AnchoredAtom0677 Fin15AnchoredAtom0963 Fin15AnchoredAtom1964 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08339
  ] at hbad
  tauto

theorem fin15Anchored_clause16157 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0481 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom1965 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16531
  ] at hbad
  tauto

theorem fin15Anchored_clause16158 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1965 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16531
  ] at hbad
  tauto

theorem fin15Anchored_clause16159 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0512 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0512 Fin15AnchoredAtom1965 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16531
  ] at hbad
  tauto

theorem fin15Anchored_clause16160 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0678 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0678 Fin15AnchoredAtom1965 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16531
  ] at hbad
  tauto

theorem fin15Anchored_clause16161 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1965 chi ∧
      ¬Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0964 Fin15AnchoredAtom1965 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16531
  ] at hbad
  tauto

theorem fin15Anchored_clause16162 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1965 chi ∧
      Fin15AnchoredAtom0481 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0512 chi ∧
      Fin15AnchoredAtom0678 chi ∧
      Fin15AnchoredAtom0964 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0481 Fin15AnchoredAtom0488 Fin15AnchoredAtom0512
    Fin15AnchoredAtom0678 Fin15AnchoredAtom0964 Fin15AnchoredAtom1965 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16531
  ] at hbad
  tauto

theorem fin15Anchored_clause16163 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00787
  ] at hbad
  tauto

theorem fin15Anchored_clause16164 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00787
  ] at hbad
  tauto

theorem fin15Anchored_clause16165 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0513 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0513 Fin15AnchoredAtom1966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00787
  ] at hbad
  tauto

theorem fin15Anchored_clause16166 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0679 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0679 Fin15AnchoredAtom1966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00787
  ] at hbad
  tauto

theorem fin15Anchored_clause16167 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1966 chi ∧
      ¬Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0965 Fin15AnchoredAtom1966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00787
  ] at hbad
  tauto

theorem fin15Anchored_clause16168 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1966 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0513 chi ∧
      Fin15AnchoredAtom0679 chi ∧
      Fin15AnchoredAtom0965 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom0483 Fin15AnchoredAtom0513
    Fin15AnchoredAtom0679 Fin15AnchoredAtom0965 Fin15AnchoredAtom1966 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask00787
  ] at hbad
  tauto

theorem fin15Anchored_clause16169 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1967 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01299
  ] at hbad
  tauto

theorem fin15Anchored_clause16170 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1967 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01299
  ] at hbad
  tauto

theorem fin15Anchored_clause16171 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0514 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0514 Fin15AnchoredAtom1967 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01299
  ] at hbad
  tauto

theorem fin15Anchored_clause16172 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0680 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0680 Fin15AnchoredAtom1967 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01299
  ] at hbad
  tauto

theorem fin15Anchored_clause16173 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1967 chi ∧
      ¬Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0966 Fin15AnchoredAtom1967 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01299
  ] at hbad
  tauto

theorem fin15Anchored_clause16174 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1967 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0514 chi ∧
      Fin15AnchoredAtom0680 chi ∧
      Fin15AnchoredAtom0966 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom0484 Fin15AnchoredAtom0514
    Fin15AnchoredAtom0680 Fin15AnchoredAtom0966 Fin15AnchoredAtom1967 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01299
  ] at hbad
  tauto

theorem fin15Anchored_clause16175 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1969 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04371
  ] at hbad
  tauto

theorem fin15Anchored_clause16176 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1969 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04371
  ] at hbad
  tauto

theorem fin15Anchored_clause16177 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1969 chi ∧
      ¬Fin15AnchoredAtom0682 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0682 Fin15AnchoredAtom1969 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04371
  ] at hbad
  tauto

theorem fin15Anchored_clause16178 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1969 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0516 chi ∧
      Fin15AnchoredAtom0682 chi ∧
      Fin15AnchoredAtom0968 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom0486 Fin15AnchoredAtom0516
    Fin15AnchoredAtom0682 Fin15AnchoredAtom0968 Fin15AnchoredAtom1969 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04371
  ] at hbad
  tauto

theorem fin15Anchored_clause16179 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1970 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08467
  ] at hbad
  tauto

theorem fin15Anchored_clause16180 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1970 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08467
  ] at hbad
  tauto

theorem fin15Anchored_clause16181 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0517 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0517 Fin15AnchoredAtom1970 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08467
  ] at hbad
  tauto

theorem fin15Anchored_clause16182 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0683 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0683 Fin15AnchoredAtom1970 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08467
  ] at hbad
  tauto

theorem fin15Anchored_clause16183 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1970 chi ∧
      ¬Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0969 Fin15AnchoredAtom1970 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08467
  ] at hbad
  tauto

theorem fin15Anchored_clause16184 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1970 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0517 chi ∧
      Fin15AnchoredAtom0683 chi ∧
      Fin15AnchoredAtom0969 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom0487 Fin15AnchoredAtom0517
    Fin15AnchoredAtom0683 Fin15AnchoredAtom0969 Fin15AnchoredAtom1970 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08467
  ] at hbad
  tauto

theorem fin15Anchored_clause16185 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0482 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom1971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16659
  ] at hbad
  tauto

theorem fin15Anchored_clause16186 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16659
  ] at hbad
  tauto

theorem fin15Anchored_clause16187 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0518 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0518 Fin15AnchoredAtom1971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16659
  ] at hbad
  tauto

theorem fin15Anchored_clause16188 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0684 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0684 Fin15AnchoredAtom1971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16659
  ] at hbad
  tauto

theorem fin15Anchored_clause16189 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1971 chi ∧
      ¬Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0970 Fin15AnchoredAtom1971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16659
  ] at hbad
  tauto

theorem fin15Anchored_clause16190 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1971 chi ∧
      Fin15AnchoredAtom0482 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0518 chi ∧
      Fin15AnchoredAtom0684 chi ∧
      Fin15AnchoredAtom0970 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0482 Fin15AnchoredAtom0488 Fin15AnchoredAtom0518
    Fin15AnchoredAtom0684 Fin15AnchoredAtom0970 Fin15AnchoredAtom1971 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16659
  ] at hbad
  tauto

theorem fin15Anchored_clause16191 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1972 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01555
  ] at hbad
  tauto

theorem fin15Anchored_clause16192 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1972 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01555
  ] at hbad
  tauto

theorem fin15Anchored_clause16193 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0519 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0519 Fin15AnchoredAtom1972 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01555
  ] at hbad
  tauto

theorem fin15Anchored_clause16194 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0685 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0685 Fin15AnchoredAtom1972 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01555
  ] at hbad
  tauto

theorem fin15Anchored_clause16195 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1972 chi ∧
      ¬Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0971 Fin15AnchoredAtom1972 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01555
  ] at hbad
  tauto

theorem fin15Anchored_clause16196 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1972 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0519 chi ∧
      Fin15AnchoredAtom0685 chi ∧
      Fin15AnchoredAtom0971 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom0484 Fin15AnchoredAtom0519
    Fin15AnchoredAtom0685 Fin15AnchoredAtom0971 Fin15AnchoredAtom1972 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask01555
  ] at hbad
  tauto

theorem fin15Anchored_clause16197 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1973 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1973 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask02579
  ] at hbad
  tauto

theorem fin15Anchored_clause16198 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04627
  ] at hbad
  tauto

theorem fin15Anchored_clause16199 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04627
  ] at hbad
  tauto

theorem fin15Anchored_clause16200 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0521 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0521 Fin15AnchoredAtom1974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04627
  ] at hbad
  tauto

theorem fin15Anchored_clause16201 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0687 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0687 Fin15AnchoredAtom1974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04627
  ] at hbad
  tauto

theorem fin15Anchored_clause16202 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1974 chi ∧
      ¬Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0973 Fin15AnchoredAtom1974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04627
  ] at hbad
  tauto

theorem fin15Anchored_clause16203 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1974 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0521 chi ∧
      Fin15AnchoredAtom0687 chi ∧
      Fin15AnchoredAtom0973 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom0486 Fin15AnchoredAtom0521
    Fin15AnchoredAtom0687 Fin15AnchoredAtom0973 Fin15AnchoredAtom1974 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask04627
  ] at hbad
  tauto

theorem fin15Anchored_clause16204 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08723
  ] at hbad
  tauto

theorem fin15Anchored_clause16205 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08723
  ] at hbad
  tauto

theorem fin15Anchored_clause16206 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0522 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0522 Fin15AnchoredAtom1975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08723
  ] at hbad
  tauto

theorem fin15Anchored_clause16207 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0688 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0688 Fin15AnchoredAtom1975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08723
  ] at hbad
  tauto

theorem fin15Anchored_clause16208 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1975 chi ∧
      ¬Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0974 Fin15AnchoredAtom1975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08723
  ] at hbad
  tauto

theorem fin15Anchored_clause16209 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1975 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0522 chi ∧
      Fin15AnchoredAtom0688 chi ∧
      Fin15AnchoredAtom0974 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom0487 Fin15AnchoredAtom0522
    Fin15AnchoredAtom0688 Fin15AnchoredAtom0974 Fin15AnchoredAtom1975 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask08723
  ] at hbad
  tauto

theorem fin15Anchored_clause16210 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0483 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom1976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16915
  ] at hbad
  tauto

theorem fin15Anchored_clause16211 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16915
  ] at hbad
  tauto

theorem fin15Anchored_clause16212 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0523 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0523 Fin15AnchoredAtom1976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16915
  ] at hbad
  tauto

theorem fin15Anchored_clause16213 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0689 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0689 Fin15AnchoredAtom1976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16915
  ] at hbad
  tauto

theorem fin15Anchored_clause16214 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1976 chi ∧
      ¬Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0975 Fin15AnchoredAtom1976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16915
  ] at hbad
  tauto

theorem fin15Anchored_clause16215 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1976 chi ∧
      Fin15AnchoredAtom0483 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0523 chi ∧
      Fin15AnchoredAtom0689 chi ∧
      Fin15AnchoredAtom0975 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0483 Fin15AnchoredAtom0488 Fin15AnchoredAtom0523
    Fin15AnchoredAtom0689 Fin15AnchoredAtom0975 Fin15AnchoredAtom1976 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask16915
  ] at hbad
  tauto

theorem fin15Anchored_clause16216 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03091
  ] at hbad
  tauto

theorem fin15Anchored_clause16217 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom0485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0485 Fin15AnchoredAtom1977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03091
  ] at hbad
  tauto

theorem fin15Anchored_clause16218 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom0524 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0524 Fin15AnchoredAtom1977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03091
  ] at hbad
  tauto

theorem fin15Anchored_clause16219 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1977 chi ∧
      ¬Fin15AnchoredAtom0690 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0690 Fin15AnchoredAtom1977 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask03091
  ] at hbad
  tauto

theorem fin15Anchored_clause16220 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05139
  ] at hbad
  tauto

theorem fin15Anchored_clause16221 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05139
  ] at hbad
  tauto

theorem fin15Anchored_clause16222 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0525 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0525 Fin15AnchoredAtom1978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05139
  ] at hbad
  tauto

theorem fin15Anchored_clause16223 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0691 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0691 Fin15AnchoredAtom1978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05139
  ] at hbad
  tauto

theorem fin15Anchored_clause16224 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1978 chi ∧
      ¬Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0977 Fin15AnchoredAtom1978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05139
  ] at hbad
  tauto

theorem fin15Anchored_clause16225 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1978 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0525 chi ∧
      Fin15AnchoredAtom0691 chi ∧
      Fin15AnchoredAtom0977 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom0486 Fin15AnchoredAtom0525
    Fin15AnchoredAtom0691 Fin15AnchoredAtom0977 Fin15AnchoredAtom1978 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask05139
  ] at hbad
  tauto

theorem fin15Anchored_clause16226 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09235
  ] at hbad
  tauto

theorem fin15Anchored_clause16227 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09235
  ] at hbad
  tauto

theorem fin15Anchored_clause16228 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0526 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0526 Fin15AnchoredAtom1979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09235
  ] at hbad
  tauto

theorem fin15Anchored_clause16229 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0692 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0692 Fin15AnchoredAtom1979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09235
  ] at hbad
  tauto

theorem fin15Anchored_clause16230 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1979 chi ∧
      ¬Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0978 Fin15AnchoredAtom1979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09235
  ] at hbad
  tauto

theorem fin15Anchored_clause16231 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1979 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0526 chi ∧
      Fin15AnchoredAtom0692 chi ∧
      Fin15AnchoredAtom0978 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom0487 Fin15AnchoredAtom0526
    Fin15AnchoredAtom0692 Fin15AnchoredAtom0978 Fin15AnchoredAtom1979 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask09235
  ] at hbad
  tauto

theorem fin15Anchored_clause16232 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0484 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom1980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17427
  ] at hbad
  tauto

theorem fin15Anchored_clause16233 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17427
  ] at hbad
  tauto

theorem fin15Anchored_clause16234 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0527 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0527 Fin15AnchoredAtom1980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17427
  ] at hbad
  tauto

theorem fin15Anchored_clause16235 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0693 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0693 Fin15AnchoredAtom1980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17427
  ] at hbad
  tauto

theorem fin15Anchored_clause16236 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1980 chi ∧
      ¬Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0979 Fin15AnchoredAtom1980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17427
  ] at hbad
  tauto

theorem fin15Anchored_clause16237 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1980 chi ∧
      Fin15AnchoredAtom0484 chi ∧
      Fin15AnchoredAtom0488 chi ∧
      Fin15AnchoredAtom0527 chi ∧
      Fin15AnchoredAtom0693 chi ∧
      Fin15AnchoredAtom0979 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0484 Fin15AnchoredAtom0488 Fin15AnchoredAtom0527
    Fin15AnchoredAtom0693 Fin15AnchoredAtom0979 Fin15AnchoredAtom1980 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask17427
  ] at hbad
  tauto

theorem fin15Anchored_clause16238 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1981 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06163
  ] at hbad
  tauto

theorem fin15Anchored_clause16239 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom0694 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0694 Fin15AnchoredAtom1981 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06163
  ] at hbad
  tauto

theorem fin15Anchored_clause16240 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1981 chi ∧
      ¬Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0980 Fin15AnchoredAtom1981 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06163
  ] at hbad
  tauto

theorem fin15Anchored_clause16241 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1981 chi ∧
      Fin15AnchoredAtom0485 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0528 chi ∧
      Fin15AnchoredAtom0694 chi ∧
      Fin15AnchoredAtom0980 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0485 Fin15AnchoredAtom0486 Fin15AnchoredAtom0528
    Fin15AnchoredAtom0694 Fin15AnchoredAtom0980 Fin15AnchoredAtom1981 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask06163
  ] at hbad
  tauto

theorem fin15Anchored_clause16242 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1982 chi ∧
      ¬Fin15AnchoredAtom0485 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0485 Fin15AnchoredAtom1982 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10259
  ] at hbad
  tauto

theorem fin15Anchored_clause16243 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1982 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1982 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10259
  ] at hbad
  tauto

theorem fin15Anchored_clause16244 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1982 chi ∧
      Fin15AnchoredAtom0485 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0529 chi ∧
      Fin15AnchoredAtom0695 chi ∧
      Fin15AnchoredAtom0981 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0485 Fin15AnchoredAtom0487 Fin15AnchoredAtom0529
    Fin15AnchoredAtom0695 Fin15AnchoredAtom0981 Fin15AnchoredAtom1982 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask10259
  ] at hbad
  tauto

theorem fin15Anchored_clause16245 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1983 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1983 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask18451
  ] at hbad
  tauto

theorem fin15Anchored_clause16246 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12307
  ] at hbad
  tauto

theorem fin15Anchored_clause16247 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0487 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0487 Fin15AnchoredAtom1984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12307
  ] at hbad
  tauto

theorem fin15Anchored_clause16248 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0531 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0531 Fin15AnchoredAtom1984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12307
  ] at hbad
  tauto

theorem fin15Anchored_clause16249 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0697 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0697 Fin15AnchoredAtom1984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12307
  ] at hbad
  tauto

theorem fin15Anchored_clause16250 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1984 chi ∧
      ¬Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0983 Fin15AnchoredAtom1984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12307
  ] at hbad
  tauto

theorem fin15Anchored_clause16251 (chi : TripleColoring 15)
    : ¬(¬Fin15AnchoredAtom1984 chi ∧
      Fin15AnchoredAtom0486 chi ∧
      Fin15AnchoredAtom0487 chi ∧
      Fin15AnchoredAtom0531 chi ∧
      Fin15AnchoredAtom0697 chi ∧
      Fin15AnchoredAtom0983 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom0487 Fin15AnchoredAtom0531
    Fin15AnchoredAtom0697 Fin15AnchoredAtom0983 Fin15AnchoredAtom1984 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask12307
  ] at hbad
  tauto

theorem fin15Anchored_clause16252 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0486 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0486 Fin15AnchoredAtom1985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20499
  ] at hbad
  tauto

theorem fin15Anchored_clause16253 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0488 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0488 Fin15AnchoredAtom1985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20499
  ] at hbad
  tauto

theorem fin15Anchored_clause16254 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0532 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0532 Fin15AnchoredAtom1985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20499
  ] at hbad
  tauto

theorem fin15Anchored_clause16255 (chi : TripleColoring 15)
    : ¬(Fin15AnchoredAtom1985 chi ∧
      ¬Fin15AnchoredAtom0698 chi) := by
  intro hbad
  unfold Fin15AnchoredAtom0698 Fin15AnchoredAtom1985 at hbad
  simp only [
    fin15Anchored_strongSet_iff_mask20499
  ] at hbad
  tauto

end ErdosSzekeres

end
