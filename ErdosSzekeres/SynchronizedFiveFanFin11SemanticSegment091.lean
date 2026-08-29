module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment090

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 091. -/

theorem synchronizedFiveFanFin11Semantic_clause06553 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0800 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0345 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0800 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06554 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0800 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0361 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0361 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0800 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06555 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0800 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0469 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0800 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06556 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1248 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0800 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0800 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1248 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06557 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0800 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0800 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06558 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1689 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0072 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0078 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0142 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0158 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0072 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0078 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0142 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0158 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1234 chi).mpr
  have hright0 : chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 7, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 6, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 7, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 7, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06559 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0800 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1689 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0800 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1689 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1234 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause06560 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0801 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0340 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0801 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0850,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06561 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0801 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0341 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0801 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0850,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06562 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0801 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0346 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0801 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0850,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06563 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0801 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0362 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0362 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0801 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0850,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06564 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0801 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0801 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0850,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06565 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1249 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0801 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0801 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06566 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1249 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0073 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0073 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1249 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0850 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06567 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1690 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0801 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0801 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1690 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06568 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0801 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1690 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0801 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1690 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0850 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause06569 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0340 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0802 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06570 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0342 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0802 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06571 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0347 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0802 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06572 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0363 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0363 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0802 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06573 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0802 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0802 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1362,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06574 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1250 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0802 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0802 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1250 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06575 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1691 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0802 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0802 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1691 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06576 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0341 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06577 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0342 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06578 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0348 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06579 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0364 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0364 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06580 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1618,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06581 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0803 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06582 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1251 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0074 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0075 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0074 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0075 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1618 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06583 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1618 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h1

theorem synchronizedFiveFanFin11Semantic_clause06584 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1618 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause06585 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1251 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1251 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1618 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause06586 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1692 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0803 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06587 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1618 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause06588 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1618 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h8)

theorem synchronizedFiveFanFin11Semantic_clause06589 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0803 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1692 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0803 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1692 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1618 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause06590 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0804 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0345 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0804 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1426,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06591 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0804 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0347 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0804 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1426,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06592 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0804 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0365 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0365 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0804 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1426,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06593 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0804 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0474 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0474 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0804 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1426,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06594 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1252 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0804 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0804 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1252 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06595 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1693 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0804 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0804 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1693 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06596 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0344 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0805 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06597 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0345 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0345 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0805 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06598 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0348 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0805 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06599 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0366 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0366 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0805 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06600 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0805 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0805 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1682,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06601 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1253 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0805 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0805 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1253 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06602 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1694 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0805 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0805 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1694 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06603 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0806 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0346 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0806 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06604 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0806 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0347 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0806 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06605 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0806 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0348 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0806 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06606 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0806 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0367 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0367 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0806 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06607 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0806 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0806 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1810,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06608 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0806 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0806 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06609 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1254 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1254 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1810 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause06610 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0806 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0806 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1695 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06611 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1695 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0064 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0066 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0079 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0080 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0081 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0064 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0066 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0079 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0080 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0081 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1695 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1810 chi).mpr
  have hright0 : chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨8, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06612 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0807 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0807 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0482,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06613 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0807 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0350 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0350 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0807 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0482,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06614 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0807 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0353 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0807 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0482,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06615 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1255 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0807 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0807 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1255 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06616 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1696 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0807 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0807 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1696 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06617 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0808 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0808 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0738,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06618 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0808 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0351 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0808 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0738,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06619 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0808 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0360 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0808 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0738,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06620 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0808 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0808 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0738,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06621 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1256 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0808 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0808 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1256 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06622 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0808 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1256 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0808 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1256 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0738 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause06623 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1697 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0808 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0808 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1697 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06624 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0809 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0349 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0809 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1250,
  ] at hbad
  tauto

end ErdosSzekeres

end
