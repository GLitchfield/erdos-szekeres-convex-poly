module

public import ErdosSzekeres.SynchronizedFiveFanFin11SemanticSegment101

@[expose] public section

set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Exact selected-core semantic clauses in bounded group 102. -/

theorem synchronizedFiveFanFin11Semantic_clause07336 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0897 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0434 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0897 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1208,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07337 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0897 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0444 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0444 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0897 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1208,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07338 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0897 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0463 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0463 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0897 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1208,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07339 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1340 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0897 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0897 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1340 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07340 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1782 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0897 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0897 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1782 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07341 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0898 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0898 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0824,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07342 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0898 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0898 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0824,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07343 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0898 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0435 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0898 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0824,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07344 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0898 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0445 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0445 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0898 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0824,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07345 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0898 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0464 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0464 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0898 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0824,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07346 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1341 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0898 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0898 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1341 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07347 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1783 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0898 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0898 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1783 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07348 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0899 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0425 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0899 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1336,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07349 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0899 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0899 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1336,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07350 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0899 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0436 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0899 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1336,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07351 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0899 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0446 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0899 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1336,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07352 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0899 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0899 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1336,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07353 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0899 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0425 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0446 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0465 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0425 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0446 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0465 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0899 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1336,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07354 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1342 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0899 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0899 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1342 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07355 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1784 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0899 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0899 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1784 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07356 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1784 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0118 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0133 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0154 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0118 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0133 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0154 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1784 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_capSet_iff_mask1336 chi).mpr
  have hright0 : chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 5, by decide, by decide⟩ <;> simp_all
  have hright1 : chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 8, by decide, by decide⟩ <;> simp_all
  have hright2 : chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 4, 10, by decide, by decide⟩ <;> simp_all
  have hright3 : chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright4 : chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright5 : chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨3, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright6 : chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 8, by decide, by decide⟩ <;> simp_all
  have hright7 : chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 5, 10, by decide, by decide⟩ <;> simp_all
  have hright8 : chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨4, 8, 10, by decide, by decide⟩ <;> simp_all
  have hright9 : chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.right := by
    cases hcolor : chi ⟨5, 8, 10, by decide, by decide⟩ <;> simp_all
  exact ⟨hright0, hright1, hright2, hright3, hright4, hright5, hright6, hright7, hright8, hright9⟩

theorem synchronizedFiveFanFin11Semantic_clause07357 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0900 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0426 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1592,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07358 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0900 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0427 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1592,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07359 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0900 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1592,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07360 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0900 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0447 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1592,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07361 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0900 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1592,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07362 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0900 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0426 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0427 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0437 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0447 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0466 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0426 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0427 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0447 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0466 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1592,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07363 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0900 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07364 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1343 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0110 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0119 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0120 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0130 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0134 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0145 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0110 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0119 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0120 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0130 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0134 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0145 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1592 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07365 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0900 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0135 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1343 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0135 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1343 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_cupSet_iff_mask1592 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact hcolor h7

theorem synchronizedFiveFanFin11Semantic_clause07366 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1785 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0900 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1785 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07367 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0900 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0155 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom1785 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0155 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0900 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1785 at hbad
  rcases hbad with ⟨hstrong, hcolor, hnotBad⟩
  apply hnotBad
  refine ⟨hstrong, ?_⟩
  intro hpure
  have hcolors := (synchronizedFiveFanFin11_capSet_iff_mask1592 chi).mp hpure
  rcases hcolors with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact Turn.noConfusion (hcolor.symm.trans h9)

theorem synchronizedFiveFanFin11Semantic_clause07368 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0901 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0901 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0472,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07369 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1344 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0901 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0901 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1344 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07370 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0902 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0428 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0902 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0728,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07371 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0902 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0902 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0728,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07372 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0902 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0433 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0433 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0902 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0728,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07373 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0902 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0449 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0449 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0902 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0728,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07374 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0902 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0468 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0468 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0902 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0728,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07375 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1345 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0902 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0902 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1345 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07376 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1345 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0112 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0121 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0126 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0136 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0141 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0157 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0112 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0121 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0126 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0136 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0141 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0157 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1345 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0728 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07377 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1786 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0902 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0902 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1786 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07378 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0903 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0428 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0428 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0903 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1240,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07379 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0903 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0903 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1240,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07380 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0903 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0434 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0434 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0903 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1240,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07381 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0903 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0450 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0450 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0903 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1240,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07382 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0903 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0469 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0469 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0903 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1240,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07383 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1346 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0903 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0903 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1346 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07384 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1787 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0903 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0903 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1787 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07385 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0904 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0904 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0856,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07386 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0904 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0904 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0856,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07387 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0904 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0435 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0435 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0904 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0856,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07388 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0904 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0451 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0451 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0904 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0856,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07389 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0904 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0470 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0470 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0904 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask0856,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07390 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1347 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0904 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0904 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1347 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07391 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1347 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0114 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0123 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0128 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0138 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0143 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0159 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0114 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0123 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0128 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0138 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0143 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0159 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1347 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask0856 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07392 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1788 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0904 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0904 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1788 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07393 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0905 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0429 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0905 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1368,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07394 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0905 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0905 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1368,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07395 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0905 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0436 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0905 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1368,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07396 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0905 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0452 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0905 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1368,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07397 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0905 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0905 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1368,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07398 (chi : TripleColoring 11)
    :
    ¬(
      ¬SynchronizedFiveFanFin11SemanticAtom0905 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0429 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0431 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0436 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0452 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0471 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0429 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0436 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0452 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0471 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0905 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1368,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07399 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0905 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0905 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07400 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1348 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0111 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0113 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0115 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0122 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0124 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0129 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0137 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0139 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0144 chi ∧
      SynchronizedFiveFanFin11SemanticAtom0160 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0111 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0113 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0115 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0122 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0124 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0129 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0137 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0139 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0144 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0160 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1348 at hbad
  rcases hbad with ⟨⟨_hstrong, hnotPure⟩,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply hnotPure
  apply (synchronizedFiveFanFin11_cupSet_iff_mask1368 chi).mpr
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem synchronizedFiveFanFin11Semantic_clause07401 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom1789 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0905 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0905 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom1789 at hbad
  exact hbad.2 hbad.1.1

theorem synchronizedFiveFanFin11Semantic_clause07402 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0430 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0430 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1624,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07403 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0431 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0431 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1624,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07404 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0437 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0437 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1624,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07405 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0453 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0453 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1624,
  ] at hbad
  tauto

theorem synchronizedFiveFanFin11Semantic_clause07406 (chi : TripleColoring 11)
    :
    ¬(
      SynchronizedFiveFanFin11SemanticAtom0906 chi ∧
      ¬SynchronizedFiveFanFin11SemanticAtom0472 chi) := by
  intro hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0472 at hbad
  unfold SynchronizedFiveFanFin11SemanticAtom0906 at hbad
  simp only [
    synchronizedFiveFanFin11_strongSet_iff_mask1624,
  ] at hbad
  tauto

end ErdosSzekeres

end
