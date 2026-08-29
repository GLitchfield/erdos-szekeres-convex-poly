module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment102

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 103. -/

theorem synchronizedFiveFanFin11Semantic_clause07407 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0906 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07408 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1349 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1624 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07409 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1624 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h3

theorem synchronizedFiveFanFin11Semantic_clause07410 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1624 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h4

theorem synchronizedFiveFanFin11Semantic_clause07411 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1624 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h6

theorem synchronizedFiveFanFin11Semantic_clause07412 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0161 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1349 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1349 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1624 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h9

theorem synchronizedFiveFanFin11Semantic_clause07413 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1790 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0906 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1790 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07414 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1790 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1790 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1624 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h0)

theorem synchronizedFiveFanFin11Semantic_clause07415 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0907 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0473 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0473 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0907 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0920,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07416 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1350 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0907 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0907 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1350 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07417 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0908 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0434 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0908 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1432,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07418 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0908 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0474 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0474 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0908 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1432,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07419 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1351 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0908 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0908 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1351 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07420 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0909 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0909 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1688,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07421 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0909 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0434 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0909 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1688,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07422 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0909 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0909 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1688,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07423 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0909 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0455 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0455 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0909 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1688,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07424 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0909 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0475 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0475 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0909 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1688,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07425 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1352 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0909 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0909 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1352 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07426 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1791 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0909 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0909 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1791 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07427 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0910 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0435 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0910 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1816,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07428 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0910 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0436 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0910 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1816,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07429 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0910 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0910 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1816,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07430 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0910 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0456 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0456 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0910 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1816,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07431 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0910 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0476 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0476 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0910 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1816,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07432 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0910 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0910 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07433 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1353 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1353 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1816 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07434 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1792 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0910 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0910 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1792 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07435 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1792 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0165 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0165 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1792 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1816 chi).mpr
  have hright0 : chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 9, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 9, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨8, 9, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07436 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0911 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0911 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0488,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07437 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0911 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0911 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0488,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07438 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1793 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0911 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0911 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1793 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07439 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0912 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0912 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07440 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0912 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0912 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07441 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0912 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0443 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0443 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0912 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07442 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0912 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0449 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0912 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07443 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0912 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0478 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0478 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0912 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0744,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07444 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1794 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0912 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0912 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1794 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07445 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0913 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0438 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0438 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0913 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1256,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07446 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0913 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0913 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1256,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07447 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0913 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0913 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1256,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07448 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0913 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0450 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0913 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1256,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07449 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0913 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0479 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0479 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0913 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1256,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07450 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1354 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0913 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0913 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1354 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07451 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1795 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0913 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0913 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1795 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07452 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0914 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0914 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07453 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0914 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0914 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07454 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0914 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0914 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07455 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0914 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0914 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07456 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0914 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0480 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0480 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0914 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0872,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07457 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1355 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0914 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0914 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1355 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07458 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0914 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0914 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07459 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1796 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0153 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0153 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask0872 chi).mpr
  have hright0 : chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 6, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 9, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 6, 9, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 9, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨6, 8, 9, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07460 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0914 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0914 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0872 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h3)

theorem synchronizedFiveFanFin11Semantic_clause07461 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0914 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0147 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1796 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0147 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0914 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1796 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask0872 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h6)

theorem synchronizedFiveFanFin11Semantic_clause07462 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0915 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0439 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0439 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0915 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1384,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07463 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0915 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0915 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1384,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07464 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0915 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0915 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1384,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07465 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0915 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0915 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1384,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07466 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0915 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0481 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0481 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0915 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1384,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07467 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1356 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0915 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0915 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1356 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07468 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1797 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0915 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0915 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1797 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07469 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0916 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0440 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0440 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0916 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1640,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07470 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0916 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0441 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0441 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0916 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1640,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07471 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0916 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0916 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1640,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07472 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0916 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0916 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1640,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07473 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0916 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0482 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0482 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0916 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1640,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07474 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1357 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0916 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0916 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07475 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1357 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0116 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0148 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0149 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0161 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0116 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0148 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0149 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0161 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1357 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1640 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07476 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1798 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0916 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0916 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1798 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07477 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0917 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0917 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0936,
  ] at hbad
  tauto

end ErdosSzekeres

end
