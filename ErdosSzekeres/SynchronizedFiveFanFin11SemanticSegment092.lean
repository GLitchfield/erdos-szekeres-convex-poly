module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment091

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 092. -/

theorem synchronizedFiveFanFin11Semantic_clause06625 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0809 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0352 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0809 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1250,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06626 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0809 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0355 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0809 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1250,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06627 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0809 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0809 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1250,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06628 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1257 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0809 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0809 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1257 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06629 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1698 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0809 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0809 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1698 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06630 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0810 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0350 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0810 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0866,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06631 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0810 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0351 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0810 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0866,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06632 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0810 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0356 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0810 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0866,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06633 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0810 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0362 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0810 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0866,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06634 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0810 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0810 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0866,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06635 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1258 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0810 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0810 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1258 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06636 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0810 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0810 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06637 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1699 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0069 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0069 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1699 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0866 chi).mpr
  have hright0 : chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06638 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0811 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0350 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0811 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1378,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06639 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0811 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0352 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0811 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1378,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06640 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0811 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0357 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0811 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1378,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06641 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0811 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0363 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0811 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1378,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06642 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0811 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0811 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1378,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06643 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1259 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0811 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0811 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1259 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06644 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1700 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0811 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0811 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1700 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06645 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0812 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0351 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0812 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1634,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06646 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0812 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0352 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0812 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1634,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06647 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0812 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0358 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0812 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1634,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06648 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0812 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0364 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0812 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1634,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06649 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0812 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0812 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1634,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06650 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0812 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0812 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06651 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1260 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0067 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0071 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0067 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0071 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1634 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06652 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0812 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1260 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0812 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1260 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1634 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause06653 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1701 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0812 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0812 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06654 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0812 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1701 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0812 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1701 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1634 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause06655 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0813 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0353 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0813 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0930,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06656 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0813 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0356 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0813 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0930,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06657 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1261 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0813 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0813 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1261 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06658 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1702 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0813 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0813 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1702 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06659 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0814 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0353 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0814 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1442,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06660 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0814 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0355 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0814 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1442,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06661 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1262 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0814 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0814 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1262 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06662 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1703 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0814 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0814 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1703 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06663 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0815 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0354 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0815 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1698,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06664 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0815 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0355 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0815 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1698,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06665 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0815 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0358 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0815 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1698,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06666 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0815 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0485 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0485 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0815 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1698,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06667 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1263 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0815 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0815 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1263 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06668 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1704 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0815 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0815 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1704 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06669 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0816 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0356 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0816 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1826,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06670 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0816 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0357 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0816 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1826,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06671 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0816 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0358 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0816 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1826,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06672 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0816 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0367 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0816 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1826,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06673 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0816 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0486 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0486 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0816 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1826,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06674 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1264 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0816 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0816 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1264 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06675 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1705 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0816 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0816 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1705 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06676 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0817 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0362 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0817 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0962,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06677 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1706 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0817 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0817 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1706 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06678 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0818 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0359 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0359 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0818 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1474,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06679 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0818 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0361 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0818 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1474,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06680 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0818 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0363 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0818 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1474,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06681 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1707 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0818 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0818 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1707 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06682 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0819 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0360 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0819 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1730,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06683 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0819 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0361 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0819 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1730,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06684 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0819 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0364 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0819 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1730,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06685 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0819 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0366 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0819 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1730,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06686 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0819 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0489 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0489 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0819 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1730,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06687 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1265 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0819 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0819 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1265 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06688 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1708 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0819 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0819 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1708 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06689 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0820 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0362 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0820 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1858,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06690 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0820 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0363 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0820 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1858,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06691 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0820 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0364 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0820 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1858,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06692 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0820 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0367 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0820 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1858,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06693 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0820 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0490 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0490 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0820 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1858,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06694 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1266 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0820 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0820 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1266 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06695 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1709 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0820 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0820 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1709 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06696 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0821 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0367 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0821 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1922,
  ] at hbad
  tauto

end ErdosSzekeres

end
