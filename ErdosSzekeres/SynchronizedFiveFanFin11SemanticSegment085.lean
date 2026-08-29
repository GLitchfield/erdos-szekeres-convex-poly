module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment084

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 085. -/

theorem synchronizedFiveFanFin11Semantic_clause06121 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1633 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0743 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0743 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1633 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06122 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0744 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0359 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0359 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0744 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0454,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06123 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0744 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0413 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0413 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0744 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0454,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06124 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1194 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0744 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0744 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1194 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06125 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1634 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0744 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0744 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1634 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06126 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0745 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0303 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0745 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0710,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06127 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0745 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0305 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0745 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0710,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06128 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0745 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0308 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0745 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0710,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06129 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0745 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0360 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0745 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0710,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06130 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0745 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0414 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0414 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0745 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0710,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06131 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1195 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0745 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0745 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1195 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06132 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0745 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0745 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1635 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06133 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1635 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0050 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0100 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0157 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0050 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0100 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0105 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1635 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0710 chi).mpr
  have hright0 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 7, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06134 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0746 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0303 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0303 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0746 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1222,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06135 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0746 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0306 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0746 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1222,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06136 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0746 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0309 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0746 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1222,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06137 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0746 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0361 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0746 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1222,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06138 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0746 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0415 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0415 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0746 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1222,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06139 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1196 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0746 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0746 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1196 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06140 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1636 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0746 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0746 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1636 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06141 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0747 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0304 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0747 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0838,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06142 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0747 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0305 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0747 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0838,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06143 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0747 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0310 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0747 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0838,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06144 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0747 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0362 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0747 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0838,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06145 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0747 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0416 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0416 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0747 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0838,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06146 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0747 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0747 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06147 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1197 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0838 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06148 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0747 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0747 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0838 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause06149 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0747 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1197 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0747 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1197 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0838 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06150 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0747 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0747 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06151 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1637 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1637 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0838 chi).mpr
  have hright0 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06152 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0748 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0304 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0304 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0748 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1350,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06153 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0748 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0306 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0748 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1350,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06154 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0748 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0311 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0748 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1350,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06155 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0748 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0363 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0748 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1350,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06156 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0748 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0417 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0417 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0748 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1350,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06157 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1198 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0748 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0748 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1198 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06158 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1198 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1198 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1350 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06159 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0748 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0748 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06160 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1638 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0101 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1350 chi).mpr
  have hright0 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06161 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0748 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1638 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0748 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1638 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1350 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause06162 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0305 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0305 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1606,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06163 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0306 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0306 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1606,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06164 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0312 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1606,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06165 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0364 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1606,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06166 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0418 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0418 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1606,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06167 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0749 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06168 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1199 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1606 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06169 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1606 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause06170 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1606 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause06171 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1606 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h8

theorem synchronizedFiveFanFin11Semantic_clause06172 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1199 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1199 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1606 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause06173 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0749 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06174 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1639 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0102 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0103 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1606 chi).mpr
  have hright0 : chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 2, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨2, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06175 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0049 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0049 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1606 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause06176 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0749 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1639 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0749 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1639 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1606 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause06177 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0750 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0307 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0307 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0750 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1414,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06178 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1640 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0750 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0750 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1640 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06179 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0751 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0308 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0308 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0751 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1670,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06180 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0751 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0309 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0309 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0751 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1670,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06181 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0751 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0312 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0751 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1670,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06182 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0751 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0366 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0751 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1670,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06183 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0751 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0421 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0421 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0751 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1670,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06184 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1200 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0751 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0751 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1200 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06185 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1641 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0751 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0751 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1641 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06186 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0752 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0310 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0310 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0752 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1798,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06187 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0752 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0311 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0311 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0752 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1798,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06188 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0752 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0312 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0312 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0752 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1798,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06189 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0752 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0367 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0752 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1798,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06190 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0752 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0422 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0422 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0752 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1798,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06191 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0752 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0752 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06192 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1201 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0051 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0052 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0053 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0108 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0109 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0051 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0052 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0053 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0107 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0108 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0109 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1201 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1798 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end ErdosSzekeres

end
