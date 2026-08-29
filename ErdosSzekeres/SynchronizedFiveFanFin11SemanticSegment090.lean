module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment089

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 090. -/

theorem synchronizedFiveFanFin11Semantic_clause06481 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0334 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0790 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0626,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06482 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0790 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0626,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06483 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0341 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0790 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0626,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06484 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0351 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0351 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0790 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0626,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06485 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0459 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0459 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0790 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0626,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06486 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1238 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0790 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0790 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06487 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1238 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0790 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1238 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask0626 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause06488 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1679 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0790 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0790 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1679 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06489 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0791 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0334 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0334 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0791 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1138,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06490 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0791 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0338 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0791 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1138,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06491 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0791 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0342 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0791 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1138,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06492 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0791 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0352 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0352 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0791 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1138,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06493 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0791 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0460 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0460 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0791 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1138,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06494 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1239 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0791 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0791 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1239 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06495 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0791 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0131 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1239 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0131 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0791 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1239 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1138 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause06496 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1680 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0791 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0791 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1680 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06497 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0792 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0792 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0434,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06498 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0792 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0343 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0343 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0792 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0434,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06499 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0792 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0353 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0353 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0792 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0434,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06500 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0792 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0461 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0461 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0792 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0434,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06501 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1240 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0792 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0792 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1240 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06502 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1681 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0792 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0792 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1681 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06503 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0793 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0335 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0793 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0690,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06504 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0793 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0793 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0690,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06505 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0793 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0344 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0793 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0690,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06506 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0793 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0354 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0354 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0793 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0690,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06507 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0793 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0462 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0462 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0793 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0690,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06508 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1241 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0793 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0793 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1241 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06509 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0793 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0793 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1682 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06510 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1682 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0061 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0063 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0065 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0068 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0070 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0077 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0132 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0151 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0061 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0063 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0065 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0068 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0070 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0077 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0132 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0151 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1682 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0690 chi).mpr
  have hright0 : chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 7, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨1, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 7, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 7, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 7, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause06511 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0794 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0335 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0335 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0794 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1202,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06512 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0794 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0338 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0794 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1202,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06513 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0794 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0355 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0355 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0794 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1202,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06514 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0794 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0463 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0794 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1202,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06515 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1242 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0794 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0794 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1242 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06516 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1683 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0794 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0794 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1683 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06517 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0795 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0795 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0818,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06518 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0795 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0795 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0818,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06519 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0795 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0346 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0346 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0795 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0818,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06520 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0795 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0356 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0356 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0795 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0818,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06521 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0795 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0795 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0818,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06522 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1243 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0795 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0795 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1243 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06523 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1684 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0795 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0795 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1684 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06524 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0336 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0336 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0796 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1330,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06525 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0338 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0796 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1330,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06526 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0347 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0347 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0796 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1330,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06527 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0357 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0357 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0796 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1330,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06528 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0796 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1330,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06529 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1244 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0796 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0796 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1244 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06530 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1685 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0796 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0796 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1685 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06531 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0337 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0337 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0797 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1586,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06532 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0338 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0338 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0797 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1586,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06533 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0348 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0348 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0797 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1586,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06534 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0358 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0358 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0797 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1586,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06535 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0797 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1586,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06536 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1245 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0797 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0797 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1245 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06537 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1686 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0797 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0797 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1686 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06538 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0798 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0340 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0340 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0798 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0466,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06539 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0798 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0359 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0359 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0798 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0466,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06540 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0798 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0467 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0467 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0798 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0466,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06541 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1246 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0798 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0798 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1246 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06542 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1687 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0798 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0798 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1687 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06543 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0799 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0339 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0799 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0722,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06544 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0799 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0341 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0341 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0799 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0722,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06545 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0799 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0344 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0344 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0799 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0722,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06546 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0799 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0360 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0360 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0799 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0722,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06547 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0799 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0799 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0722,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06548 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1247 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0799 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0799 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1247 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06549 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1688 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0799 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0799 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1688 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause06550 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0799 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0062 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1688 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0062 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0799 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1688 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0722 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause06551 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0800 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0339 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0339 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0800 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1234,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause06552 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0800 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0342 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0342 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0800 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1234,
  ] at hbad
  tauto

end ErdosSzekeres

end
