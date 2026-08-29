module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment074

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 075. -/

theorem synchronizedFiveFanFin11Semantic_clause05401 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0649 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0649 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1129,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05402 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0649 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0244 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0649 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1129,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05403 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0649 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0268 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0268 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0649 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1129,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05404 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0649 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0649 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1129,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05405 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1101 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0649 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0649 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1101 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05406 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1101 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0031 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0039 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0031 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0039 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1101 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1129 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05407 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1542 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0649 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0649 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1542 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05408 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0650 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0269 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0269 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0650 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0425,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05409 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0650 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0442 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0442 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0650 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0425,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05410 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1102 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0650 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0650 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1102 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05411 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1543 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0650 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0650 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1543 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05412 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0651 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0651 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0681,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05413 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0651 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0270 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0270 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0651 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0681,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05414 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1103 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0651 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0651 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1103 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05415 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1544 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0651 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0651 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1544 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05416 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0652 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0237 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0237 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0652 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1193,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05417 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0652 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0652 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1193,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05418 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0652 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0246 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0246 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0652 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1193,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05419 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0652 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0271 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0271 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0652 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1193,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05420 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0652 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0652 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1193,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05421 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1104 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0652 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0652 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1104 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05422 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1545 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0652 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0652 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1545 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05423 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0653 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0238 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0653 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05424 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0653 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0653 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05425 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0653 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0247 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0653 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05426 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0653 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0272 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0272 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0653 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05427 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0653 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0653 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0809,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05428 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1105 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0653 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0653 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1105 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05429 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1546 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0653 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0653 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1546 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05430 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1546 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0033 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0033 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1546 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0809 chi).mpr
  have hright0 : chi ⟨0, 3, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨0, 3, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨0, 3, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 3, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨0, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨0, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨0, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨0, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause05431 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0653 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1546 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0653 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1546 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0809 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause05432 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0653 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1546 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0653 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1546 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0809 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause05433 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0654 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0238 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0238 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0654 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1321,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05434 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0654 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0654 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1321,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05435 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0654 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0248 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0654 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1321,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05436 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0654 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0273 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0273 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0654 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1321,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05437 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0654 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0654 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1321,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05438 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1106 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0654 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0654 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1106 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05439 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1547 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0654 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0654 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1547 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05440 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0655 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0239 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0655 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1577,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05441 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0655 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0240 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0240 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0655 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1577,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05442 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0655 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0249 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0249 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0655 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1577,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05443 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0655 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0274 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0274 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0655 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1577,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05444 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0655 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0655 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1577,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05445 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1107 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0655 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0655 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1107 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05446 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1107 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0019 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0024 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0034 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0035 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0045 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0019 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0024 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0034 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0035 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0045 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1107 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1577 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05447 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1548 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0655 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0655 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1548 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05448 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0656 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0243 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0656 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0713,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05449 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0656 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0449 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0656 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0713,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05450 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1108 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0656 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0656 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1108 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05451 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1549 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0656 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0656 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1549 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05452 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0657 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0244 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0657 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1225,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05453 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0657 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0277 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0277 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0657 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1225,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05454 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0657 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0450 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0657 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1225,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05455 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1109 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0657 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0657 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1109 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05456 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1550 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0657 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0657 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1550 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05457 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0242 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0841,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05458 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0243 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0243 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0841,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05459 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0247 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0247 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0841,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05460 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0278 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0278 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0841,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05461 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0841,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05462 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0658 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1110 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05463 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0022 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0038 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0043 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0022 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0038 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0043 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1110 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0841 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause05464 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0020 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1110 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0020 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1110 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0841 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h0

theorem synchronizedFiveFanFin11Semantic_clause05465 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0658 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1110 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1110 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0841 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause05466 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1551 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0658 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1551 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause05467 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0658 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0023 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1551 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0023 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1551 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0841 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h2)

theorem synchronizedFiveFanFin11Semantic_clause05468 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0658 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0037 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1551 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0037 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0658 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1551 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0841 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause05469 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0242 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0242 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0659 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1353,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05470 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0244 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0244 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0659 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1353,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05471 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0248 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0248 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0659 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1353,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause05472 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0659 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0279 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0279 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0659 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1353,
  ] at hbad
  tauto

end ErdosSzekeres

end
